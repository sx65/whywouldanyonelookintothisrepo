-- language: Luau, file: bladeball_kuroko.luau, target: Blade Ball (13772394625) build 6376, executor: MacSploit 741.2+
-- BAC notes: sensor = VM module "SwordsController \f.PRY" (report codes 494kjkdf / 64565gfdd).
-- Parries ship through the game's own signed sender (dual-path, uid + TIME xor sig) -> server sees authentic traffic.

--// services
local Players = game:GetService("Players")
local RunService = game:GetService("RunService")
local UserInputService = game:GetService("UserInputService")
local Stats = game:GetService("Stats")
local TweenService = game:GetService("TweenService")
local ReplicatedStorage = game:GetService("ReplicatedStorage")
local HttpService = game:GetService("HttpService")
local Debris = game:GetService("Debris")
local LocalPlayer = Players.LocalPlayer

--// config
local CONFIG_PATH = "kuroko_bladeball.json"
local DEFAULTS = {
	auto_parry = true,
	accuracy = 100,
	auto_spam = false,
	spam_threshold = 0,
	manual_spam = false,
	manual_kps = 100,
	curve_method = "Camera",
	random_target = false,
	det_holds = true,
	anti_phantom = false, -- tweens HRP behind the ball; server position validation is the risk surface
	anim_fix = false,
	-- combat intelligence
	ability_enabled = false,
	ability_delay = 0.15,
	ability_cooldown = 1.5,
	ability_whiff = true,
	ability_dodge = false,
	reaction_pull = true,
	reaction_stance = true,
	calibrator = true,
	curve_defense = true,
	auto_curve_pick = false,
	auto_emote = false,
	-- movement
	move_optimizer = false,
	-- visuals
	esp_enabled = false,
	spectator_hud = false,
	staff_names = "",
	feed_enabled = false,
	feed_prefix = ">> ",
	-- lobby / economy
	crate_opener = false,
	crate_count = 1,
	crate_delay = 2,
	auto_claim = false,
	auto_spin = false,
}
local config = table.clone(DEFAULTS)

local function save_config()
	pcall(function()
		writefile(CONFIG_PATH, HttpService:JSONEncode(config))
	end)
end

do
	local ok, data = pcall(function()
		return HttpService:JSONDecode(readfile(CONFIG_PATH))
	end)
	if ok and type(data) == "table" then
		for key, value in pairs(DEFAULTS) do
			if type(data[key]) == type(value) then
				config[key] = data[key]
			end
		end
	end
end

--// ============ BAC layer ============

local bac = {
	sender = nil, -- installed VM send syscall: signs (uid, TIME-sig) and fans out over its redundant remotes
	token_fn = nil, -- uid -> "TIME" key decoder (sender upvalue)
	captured = nil, -- fallback: one recorded legit send { remote, args }
	path = "key",
}

-- the hardened sender is the only closure carrying both report codes
local function find_sender()
	local fallback = nil
	for _, obj in ipairs(getgc(true)) do
		if type(obj) == "function" and islclosure(obj) then
			local ok, consts = pcall(getconstants, obj)
			if ok and type(consts) == "table" then
				local has_a, has_b, has_time, has_writefile, has_snt = false, false, false, false, false
				for _, c in ipairs(consts) do
					if c == "494kjkdf" then
						has_a = true
					elseif c == "64565gfdd" then
						has_b = true
					elseif c == "TIME" then
						has_time = true
					elseif c == "writefile" then
						has_writefile = true
					elseif c == "GetServerTimeNow" then
						has_snt = true
					end
				end
				if has_a and has_b then
					return obj
				end
				if has_time and has_writefile and has_snt then
					fallback = obj
				end
			end
		end
	end
	return fallback
end

-- kill the getfenv(1..10)/writefile stack walk two ways: the field-match constant and the env-fetch global.
-- nested pcall in the original swallows the renamed global -> check fails closed, sender keeps signing.
local function neuter_sensor(sender)
	local ok, consts = pcall(getconstants, sender)
	if ok and type(consts) == "table" then
		for i, c in ipairs(consts) do
			if c == "writefile" then
				pcall(setconstant, sender, i, "__wf_neutered")
			end
		end
	end
	local ok_p, protos = pcall(getprotos, sender)
	if ok_p and type(protos) == "table" then
		for _, proto in ipairs(protos) do
			local ok_c, pconsts = pcall(getconstants, proto)
			if ok_c and type(pconsts) == "table" then
				for i, c in ipairs(pconsts) do
					if c == "getfenv" then
						pcall(setconstant, proto, i, "__gone_env")
					end
				end
			end
		end
	end
end

-- token decoder = the function-shaped upvalue of the sender; falls back to the community PRY-source scan
local function find_token_fn(sender)
	if sender then
		local ok, ups = pcall(getupvalues, sender)
		if ok and type(ups) == "table" then
			for _, value in ipairs(ups) do
				if type(value) == "function" then
					return value
				end
			end
		end
	end
	for _, obj in ipairs(getgc(true)) do
		if type(obj) == "function" and islclosure(obj) then
			local ok_src, src = pcall(debug.info, obj, "s")
			if ok_src and type(src) == "string" and src:find("PRY", 1, true) then
				local ok_ups, ups = pcall(getupvalues, obj)
				if ok_ups and type(ups) == "table" then
					for _, value in ipairs(ups) do
						if type(value) == "function" then
							return value
						end
					end
				end
			end
		end
	end
	return nil
end

-- exact BAC TIME signature: xor each digit of floor(serverTime*100) with the uid-derived key
local function tokenize(uid)
	local time = tostring(math.floor(workspace:GetServerTimeNow() * 100))
	local key = bac.token_fn(uid, "TIME")
	local chars = table.create(#time)
	for index = 1, #time do
		chars[index] = string.char(bit32.bxor((string.byte(time, index) + index) % 256, string.byte(key, (index - 1) % #key + 1)))
	end
	return table.concat(chars)
end

-- fallback capture: record the first legit 8-arg parry send (uid lives in args[2]); callee-side only,
-- never sits above game frames so the env walk cannot see it even unpatched
local function install_capture()
	local captured = {}
	local hooked = {}
	local ok_mt, meta = pcall(getrawmetatable, game)
	if not ok_mt or type(meta) ~= "table" then
		return
	end
	pcall(function()
		setreadonly(meta, false)
		local old_index = meta.__index
		meta.__index = newcclosure(function(self, key)
			if (key == "FireServer" and self:IsA("RemoteEvent")) or (key == "InvokeServer" and self:IsA("RemoteFunction")) then
				if not hooked[self] then
					hooked[self] = true
					local original = old_index(self, key)
					return newcclosure(function(_, ...)
						local args = { ... }
						if #args == 8 and type(args[2]) == "string" and type(args[3]) == "string" and type(args[4]) == "number" and typeof(args[5]) == "CFrame" and type(args[6]) == "table" and type(args[7]) == "table" and type(args[8]) == "boolean" then
							if not bac.captured then
								bac.captured = { remote = self, args = args }
							end
						end
						return original(_, table.unpack(args))
					end)
				end
			end
			return old_index(self, key)
		end)
		setreadonly(meta, true)
	end)
	bac.capture_installed = true
end

--// ============ parry input ============
-- the press goes through the engine: the game's own handler gates it by state and signs the send,
-- so input telemetry and remote telemetry always agree. remote tiers stay as verified fallback.

local vim_instance = nil
local function get_vim()
	if vim_instance then
		return vim_instance
	end
	local ok, vim = pcall(function()
		return Instance.new("VirtualInputManager")
	end)
	if ok then
		vim_instance = vim
	end
	return vim_instance
end

-- the game broadcasts every parry press it accepts; absence of the echo = the engine refused
local parry_confirmation = 0
pcall(function()
	local remotes = ReplicatedStorage:FindFirstChild("Remotes", true)
	local attempt = remotes and remotes:FindFirstChild("ParryAttemptAll")
	if attempt then
		attempt.OnClientEvent:Connect(function(_, character)
			if character == LocalPlayer.Character then
				parry_confirmation = tick()
			end
		end)
	end
end)

local path_tiers = { "key", "mouse", "sender", "replay" }
local path_index = 1
local last_fire_at = 0
local unconfirmed = 0

local function press_key(keycode)
	keycode = keycode or Enum.KeyCode.F
	local vim = get_vim()
	if not vim then
		return false
	end
	pcall(function()
		vim:SendKeyEvent(true, keycode, false, game)
	end)
	task.delay(0.03, function()
		pcall(function()
			vim:SendKeyEvent(false, keycode, false, game)
		end)
	end)
	return true
end

local function press_mouse()
	if mouse1press and mouse1release then
		pcall(mouse1press)
		task.delay(0.03, function()
			pcall(mouse1release)
		end)
		return true
	end
	if mouse1click then
		return pcall(mouse1click)
	end
	return false
end

local function fire_parry(curve_cframe, screen_positions, mouse_loc)
	-- degrade a tier when the engine swallowed two consecutive presses
	if last_fire_at > 0 and parry_confirmation < last_fire_at and (tick() - last_fire_at) > 0.35 then
		unconfirmed += 1
		if unconfirmed >= 2 and path_index < #path_tiers then
			path_index += 1
			unconfirmed = 0
		end
	else
		unconfirmed = 0
	end

	local tier = path_tiers[path_index]
	bac.path = tier

	if tier == "key" then
		last_fire_at = tick()
		local ok = press_key()
		if not ok then
			path_index += 1
		end
		return ok
	elseif tier == "mouse" then
		last_fire_at = tick()
		local ok = press_mouse()
		if not ok then
			path_index += 1
		end
		return ok
	elseif tier == "sender" and bac.sender then
		last_fire_at = tick()
		local ok = pcall(bac.sender, 0.5, curve_cframe, screen_positions, mouse_loc, false)
		if ok then
			return true
		end
		path_index += 1
	end

	if bac.token_fn and bac.captured then
		local captured = bac.captured
		last_fire_at = tick()
		bac.path = "replay"
		local ok = pcall(function()
			captured.remote:FireServer(
				captured.args[1],
				captured.args[2],
				tokenize(captured.args[2]),
				0.5,
				curve_cframe,
				screen_positions,
				mouse_loc,
				false
			)
		end)
		return ok
	end

	last_fire_at = tick()
	bac.path = "mouse"
	return press_mouse()
end

task.spawn(function()
	for _ = 1, 40 do
		bac.sender = find_sender()
		if bac.sender then
			break
		end
		task.wait(1)
	end
	if bac.sender then
		neuter_sensor(bac.sender)
	else
		install_capture()
	end
	bac.token_fn = find_token_fn(bac.sender)
	bac.path = "key"
end)

--// ============ ball model ============

local ball_props = {
	aerodynamic_time = tick(),
	last_warping = tick(),
	lerp_radians = 0,
	curving = tick(),
}

local function linear_predict(a, b, t)
	return a + (b - a) * t
end

local function get_ball()
	for _, ball in ipairs(workspace.Balls:GetChildren()) do
		if ball:GetAttribute("realBall") then
			return ball
		end
	end
end

--// ============ round-state gate ============
-- the game's own parry input refuses to fire outside a live chase; the syscall call skips that
-- gate, so every send must be state-gated here or the server sees validly-signed impossible parries

local round_guard_until = 0

local function in_round()
	if tick() < round_guard_until then
		return false
	end
	local character = LocalPlayer.Character
	local hrp = character and character.PrimaryPart
	if not (hrp and character.Parent == workspace:FindFirstChild("Alive")) then
		return false
	end
	local ball = get_ball()
	if not ball then
		return false
	end
	local target = ball:GetAttribute("target")
	if not target or not Players:FindFirstChild(target) then
		return false
	end
	local zoomies = ball:FindFirstChild("zoomies")
	-- frozen ball = chase over (win screen / reset); the game would not accept input here either
	if not zoomies or zoomies.VectorVelocity.Magnitude <= 1 then
		return false
	end
	return true
end

local function ball_curved_for(ball)
	if not ball then
		return false
	end
	local zoomies = ball:FindFirstChild("zoomies")
	if not zoomies then
		return false
	end
	local character = LocalPlayer.Character
	local hrp = character and character.PrimaryPart
	if not hrp then
		return false
	end

	local velocity = zoomies.VectorVelocity
	local speed = velocity.Magnitude
	if speed <= 0 then
		return false
	end
	local vel_unit = velocity.Unit
	local to_me = (hrp.Position - ball.Position).Unit
	local dot_product = to_me:Dot(vel_unit)
	local accel_dir = (vel_unit - velocity).Unit
	local dot_difference = dot_product - to_me:Dot(accel_dir)
	local distance = (hrp.Position - ball.Position).Magnitude
	local ping_ms = Stats.Network.ServerStatsItem["Data Ping"]:GetValue()
	local ping_threshold = 0.5 - (ping_ms / 1000)
	local time_to_impact = distance / speed - (ping_ms / 1000)
	local speed_factor = math.min(speed / 100, 40)
	local min_distance = 15 - math.min(distance / 1000, 15) + speed_factor

	local angle_rad = math.asin(math.clamp(dot_product, -1, 1))
	ball_props.lerp_radians = linear_predict(ball_props.lerp_radians, angle_rad, 0.8)

	if speed > 100 and time_to_impact > ping_ms / 10 then
		min_distance = math.max(min_distance - 15, 15)
	end
	if distance < min_distance then
		return false
	end
	if dot_difference < ping_threshold then
		return true
	end
	if ball_props.lerp_radians < 0.018 then
		ball_props.last_warping = tick()
	end
	if (tick() - ball_props.last_warping) < (time_to_impact / 1.5) then
		return true
	end
	if (tick() - ball_props.curving) < (time_to_impact / 1.5) then
		return true
	end
	return dot_product < ping_threshold
end

local function ball_curved()
	return ball_curved_for(get_ball())
end

--// ============ targeting ============

local current_target = nil
local recently_picked = {}

local function select_target_by_mouse()
	local camera = workspace.CurrentCamera
	local mouse_pos = UserInputService:GetMouseLocation()
	local ray = camera:ScreenPointToRay(mouse_pos.X, mouse_pos.Y)
	local best, best_dot = nil, -math.huge
	for _, char in ipairs(workspace.Alive:GetChildren()) do
		if char.Name ~= LocalPlayer.Name and char.PrimaryPart then
			local dot = ray.Direction:Dot((char.PrimaryPart.Position - camera.CFrame.Position).Unit)
			if dot > best_dot then
				best_dot = dot
				best = char
			end
		end
	end
	current_target = best
	return best
end

local function pick_random_target()
	local living = {}
	for _, char in ipairs(workspace.Alive:GetChildren()) do
		if char.Name ~= LocalPlayer.Name and char.PrimaryPart and not recently_picked[char.Name] then
			table.insert(living, char)
		end
	end
	if #living == 0 then
		recently_picked = {}
		for _, char in ipairs(workspace.Alive:GetChildren()) do
			if char.Name ~= LocalPlayer.Name and char.PrimaryPart then
				table.insert(living, char)
			end
		end
	end
	if #living == 0 then
		current_target = nil
		return
	end
	local picked = living[math.random(1, #living)]
	recently_picked[picked.Name] = true
	current_target = picked
end

--// ============ parry payload ============

local function get_curve_cframe()
	local camera = workspace.CurrentCamera
	local character = LocalPlayer.Character
	local hrp = character and character:FindFirstChild("HumanoidRootPart")
	if not hrp then
		return camera.CFrame
	end
	local method = config.curve_method
	local target = current_target
	local target_pos = (target and target.PrimaryPart and target.PrimaryPart.Position)
		or (hrp.Position + camera.CFrame.LookVector * 1000)
	local to_target = (target_pos - hrp.Position).Unit

	-- A4: auto curve pick - counter the target's bearing instead of running one fixed method
	if config.auto_curve_pick and target and target.PrimaryPart then
		local facing = camera.CFrame.LookVector:Dot(to_target)
		if facing < -0.2 then
			method = "Backwards" -- target behind the swing: flip the curve
		elseif facing > 0.7 then
			method = "Dot" -- centered: curve straight through
		else
			method = "Random" -- wide angles: keep the deflection unreadable
		end
	end

	if method == "Dot" then
		return CFrame.lookAt(hrp.Position, target_pos + Vector3.new(0, 1.75, 0))
	elseif method == "Backwards" then
		return CFrame.new(hrp.Position, hrp.Position - to_target * 1000)
	elseif method == "Slow" then
		return CFrame.new(hrp.Position, hrp.Position + Vector3.new(0, -350, 0))
	elseif method == "Random" then
		return CFrame.new(hrp.Position, target_pos + Vector3.new(math.random(-1000, 1000), math.random(-350, 1000), math.random(-1000, 1000)))
	end
	return camera.CFrame
end

local parry_count = 0
local parry_active = false
local ball_fired_at = setmetatable({}, { __mode = "k" })

local function do_parry()
	if not in_round() then
		return false
	end
	if parry_count >= 8 then
		return false
	end
	if config.random_target then
		if not (current_target and current_target.PrimaryPart) then
			pick_random_target()
		end
	else
		select_target_by_mouse()
	end

	local camera = workspace.CurrentCamera
	local curve_cframe = get_curve_cframe()

	local mouse_loc
	if config.random_target and current_target and current_target.PrimaryPart then
		local viewport = camera:WorldToViewportPoint(current_target.PrimaryPart.Position)
		mouse_loc = { viewport.X, viewport.Y }
	else
		local mp = UserInputService:GetMouseLocation()
		mouse_loc = { mp.X, mp.Y }
	end

	local screen_positions = {}
	for _, char in ipairs(workspace.Alive:GetChildren()) do
		if char.PrimaryPart then
			local ok, screen_pt = pcall(function()
				return camera:WorldToScreenPoint(char.PrimaryPart.Position)
			end)
			if ok then
				screen_positions[char.Name] = screen_pt
			end
		end
	end

	local fired = fire_parry(curve_cframe, screen_positions, mouse_loc)

	parry_count += 1
	task.delay(0.5, function()
		parry_count -= 1
	end)
	return fired
end

--// ============ ability detectors (verified remotes only) ============

local det = {
	infinity = false,
	death_slash = false,
	pull = false,
	slash_cape = false,
}

local function wire(remote_name, handler)
	local remote = ReplicatedStorage:FindFirstChild("Remotes", true)
	remote = remote and remote:FindFirstChild(remote_name)
	if remote then
		pcall(function()
			remote.OnClientEvent:Connect(handler)
		end)
	end
end

wire("InfinityBall", function(_, state)
	det.infinity = state == true
end)
wire("DeathBall", function(_, state)
	det.death_slash = state == true
end)
wire("PlrPulled", function(a, b)
	if type(a) == "boolean" then
		det.pull = a
	elseif type(b) == "boolean" then
		det.pull = b
	else
		det.pull = true
		task.delay(1.5, function()
			det.pull = false
		end)
	end
end)
wire("PlrPulsed", function(a, b)
	if type(a) == "boolean" then
		det.pull = a
	elseif type(b) == "boolean" then
		det.pull = b
	end
end)

local function holds_active()
	if not config.det_holds then
		return false
	end
	local character = LocalPlayer.Character
	local hrp = character and character.PrimaryPart
	det.slash_cape = hrp ~= nil and hrp:FindFirstChild("SingularityCape") ~= nil
	if det.infinity or det.death_slash or det.pull or det.slash_cape then
		return true
	end
	local runtime = workspace:FindFirstChild("Runtime")
	local tornado = runtime and runtime:FindFirstChild("Tornado")
	if tornado and (tick() - ball_props.aerodynamic_time) < (tornado:GetAttribute("TornadoTime") or 1) + 3.14159 then
		return true
	end
	return false
end

--// ============ spam geometry (hub-exact) ============

local function spam_range()
	local ball = get_ball()
	local character = LocalPlayer.Character
	local hrp = character and character.PrimaryPart
	if not (ball and hrp and current_target and current_target.PrimaryPart) then
		return 0
	end
	local zoomies = ball:FindFirstChild("zoomies")
	local velocity = zoomies and zoomies.VectorVelocity or ball.AssemblyLinearVelocity
	local speed = velocity.Magnitude
	local to_me = (hrp.Position - ball.Position).Unit
	local dot = to_me:Dot(velocity.Unit)
	local ping_clamped = math.clamp(Stats.Network.ServerStatsItem["Data Ping"]:GetValue() / 10, 1, 16)
	local max_dist = ping_clamped + math.min(speed / 6, 95)

	local target_dist = LocalPlayer:DistanceFromCharacter(current_target.PrimaryPart.Position)
	local ball_dist = LocalPlayer:DistanceFromCharacter(ball.Position)
	if target_dist > max_dist or ball_dist > max_dist then
		return 0
	end
	local max_dot = math.clamp(dot, -1, 0) * (5 - math.min(speed / 5, 5))
	return max_dist - max_dot
end

--// ============ timing core ============
-- W matches the 0.5 the game itself sends in the parry payload (the swing's active duration)
local PARRY_WINDOW = 0.5

local ping_ema = 0
local function rtt_seconds()
	local raw = Stats.Network.ServerStatsItem["Data Ping"]:GetValue() / 1000
	if ping_ema == 0 then
		ping_ema = raw
	end
	ping_ema = ping_ema * 0.85 + raw * 0.15
	-- worst of instant/ema + engine & frame quantization slack, capped at 600ms
	return math.clamp(math.max(raw, ping_ema) + 0.025, 0.01, 0.6)
end

-- closing rate, not speed magnitude: a ball crossing behind you closes slowly, one you
-- strafe into closes fast - only the radial component decides time of arrival
local function time_to_contact(ball, hrp)
	local zoomies = ball:FindFirstChild("zoomies")
	if not zoomies then
		return nil, 0
	end
	local velocity = zoomies.VectorVelocity
	local to_hrp = hrp.Position - ball.Position
	local distance = to_hrp.Magnitude
	if distance <= 0 then
		return 0, velocity.Magnitude
	end
	local closing_rate = -velocity:Dot(to_hrp.Unit)
	if closing_rate <= 1 then
		return nil, velocity.Magnitude
	end
	return distance / closing_rate, velocity.Magnitude
end

--// ============ perfect-parry calibrator ============
-- every press logs (ttc, rtt); the ParrySuccess echo marks success. failures shift the window
-- fraction toward safety in the direction the miss came from (late -> earlier, early -> later).

local press_stats = {
	bias = 0, -- frac correction, clamped
	hits = 0,
	total = 0,
	last_press = nil, -- { ttc, rtt, at }
}

local function timing_frac()
	local base = 0.65 - (config.accuracy / 100) * 0.15
	return math.clamp(base + press_stats.bias, 0.3, 0.85)
end

local function record_press(ttc)
	press_stats.last_press = { ttc = ttc, rtt = rtt_seconds(), at = tick() }
	press_stats.total += 1
end

local function record_parry_result(success)
	local press = press_stats.last_press
	if not press or (tick() - press.at) > 1 then
		return
	end
	if success then
		press_stats.hits += 1
		return
	end
	-- late miss: press landed after the window; move the trigger earlier (larger frac)
	-- early miss: swing expired before contact; move later (smaller frac)
	if not config.calibrator then
		return
	end
	if press.ttc and press.ttc < press.rtt + PARRY_WINDOW * 0.2 then
		press_stats.bias = math.clamp(press_stats.bias + 0.02, -0.15, 0.15)
	else
		press_stats.bias = math.clamp(press_stats.bias - 0.02, -0.15, 0.15)
	end
end

--// ============ ability engine ============
-- A1/A2/B6/B7/B9: Q casts on combo/whiff/reaction/dodge triggers. input synthesis only.

local ability_state = {
	last_cast = 0,
	last_emote = 0,
}
local hooks = { feed = nil, notify = nil }
local last_success_by_hrp = {}

local function cast_ability()
	if not config.ability_enabled then
		return false
	end
	if holds_active() or not in_round() then
		return false
	end
	if tick() - ability_state.last_cast < config.ability_cooldown then
		return false
	end

	local character = LocalPlayer.Character
	local hrp = character and character.PrimaryPart
	local humanoid = character and character:FindFirstChildOfClass("Humanoid")
	-- B9: brief move intent toward the target before the cast (line-up assist)
	if humanoid and current_target and current_target.PrimaryPart and hrp then
		humanoid:Move((current_target.PrimaryPart.Position - hrp.Position).Unit)
		task.delay(0.1, function()
			pcall(function()
				humanoid:Move(Vector3.zero)
			end)
		end)
	end

	ability_state.last_cast = tick()
	return press_key(Enum.KeyCode.Q)
end

local DASH_ABILITIES = {
	["Dash"] = true,
	["Thunder Dash"] = true,
	["Ninja Dash"] = true,
	["Super Jump"] = true,
	["Bunny Leap"] = true,
}

local function dodge_cast()
	if not config.ability_dodge then
		return false
	end
	local equipped = LocalPlayer:GetAttribute("CurrentlyEquippedAbility")
	if not (equipped and DASH_ABILITIES[equipped]) then
		return false
	end
	return cast_ability()
end

pcall(function()
	local remotes = ReplicatedStorage:FindFirstChild("Remotes", true)
	if not remotes then
		return
	end

	local success_all = remotes:FindFirstChild("ParrySuccessAll")
	if success_all then
		success_all.OnClientEvent:Connect(function(_, parrier)
			local character = LocalPlayer.Character
			local my_hrp = character and character.PrimaryPart
			if parrier and parrier:IsA("BasePart") then
				last_success_by_hrp[parrier] = tick()
			end
			if parrier == my_hrp then
				record_parry_result(true)
				if config.ability_enabled then
					task.delay(config.ability_delay, cast_ability)
				end
			end
		end)
	end

	local attempt_all = remotes:FindFirstChild("ParryAttemptAll")
	if attempt_all then
		attempt_all.OnClientEvent:Connect(function(_, model)
			local character = LocalPlayer.Character
			local my_model = character
			if model == my_model then
				return
			end
			-- A1 whiff read: an attempt with no success echo inside 300ms is a missed swing
			local their_hrp = model and model.PrimaryPart
			local at = tick()
			task.delay(0.3, function()
				if config.ability_whiff and their_hrp and (last_success_by_hrp[their_hrp] or 0) < at then
					cast_ability()
				end
			end)
		end)
	end

	local exploded = remotes:FindFirstChild("BallExplode")
	if exploded then
		exploded.OnClientEvent:Connect(function(_, player)
			if player == LocalPlayer then
				record_parry_result(false)
				return
			end
			-- A6: emote on a kill that followed our parry
			if config.auto_emote and tick() - (press_stats.last_press and press_stats.last_press.at or 0) < 3 then
				if tick() - ability_state.last_emote > 2 then
					ability_state.last_emote = tick()
					press_key(Enum.KeyCode.R)
				end
			end
			if hooks.feed and player and player.Name then
				hooks.feed(player.Name .. " was eliminated")
			end
		end)
	end

	-- A2: counter-cast when the pull releases and when a death-slash stance drops
	pcall(function()
		local pulled = remotes:FindFirstChild("PlrPulled")
		if pulled then
			pulled.OnClientEvent:Connect(function(a, b)
				local active = (type(a) == "boolean" and a) or (type(b) == "boolean" and b) or false
				if active and config.reaction_pull and config.ability_enabled then
					task.delay(0.35, cast_ability)
				end
			end)
		end
	end)
end)

LocalPlayer.CharacterAdded:Connect(function(character)
	character:GetAttributeChangedSignal("DEATH_SLASH_STANCE"):Connect(function()
		local stance = character:GetAttribute("DEATH_SLASH_STANCE")
		if not stance and config.reaction_stance and config.ability_enabled then
			task.delay(0.15, cast_ability)
		end
	end)
end)

--// ============ movement optimizer ============
-- B8: move intent away from the ball's approach while it hunts us; hands off inside the
-- parry window so the swing timing is never disturbed. Humanoid:Move is client intent only.

local move_engaged = false
local function movement_step(hrp, ball, ttc)
	local humanoid = LocalPlayer.Character and LocalPlayer.Character:FindFirstChildOfClass("Humanoid")
	if not humanoid then
		return
	end
	local engaged = config.move_optimizer and in_round() and ttc ~= nil and ttc > 0.5
		and ball:GetAttribute("target") == LocalPlayer.Name
	if engaged then
		local away = (hrp.Position - ball.Position)
		away = Vector3.new(away.X, 0, away.Z)
		if away.Magnitude > 0.1 then
			humanoid:Move(away.Unit)
			move_engaged = true
			return
		end
	end
	-- edge-triggered release: one neutral move when the chase ends, then hands off entirely
	if move_engaged then
		move_engaged = false
		humanoid:Move(Vector3.zero)
	end
end

--// ============ loops ============

local last_spam_fire = 0
local last_manual_fire = 0

RunService.PreSimulation:Connect(function()
	local character = LocalPlayer.Character
	local hrp = character and character.PrimaryPart
	if not hrp then
		return
	end

	if not in_round() then
		parry_active = false
		return
	end

	local ball = get_ball()
	if not ball then
		return
	end
	local zoomies = ball:FindFirstChild("zoomies")
	if not zoomies then
		return
	end

	if config.move_optimizer then
		movement_step(hrp, ball, time_to_contact(ball, hrp))
	end

	-- animation fix: kill the grab track that eats the visual parry window
	if config.anim_fix then
		pcall(function()
			local humanoid = character:FindFirstChildOfClass("Humanoid")
			local animator = humanoid and humanoid:FindFirstChildOfClass("Animator")
			if animator then
				for _, track in ipairs(animator:GetPlayingAnimationTracks()) do
					if track.Name == "GrabParry" or track.Name == "Grab" then
						track:Stop(track:GetAttribute("StopFadeTime") or 0.1)
					end
				end
			end
		end)
	end

	if config.auto_parry then
		-- A5: independent windows per ball, most urgent first
		local candidates = {}
		for _, target_ball in ipairs(workspace.Balls:GetChildren()) do
			local target_zoomies = target_ball:FindFirstChild("zoomies")
			if target_zoomies and target_ball:GetAttribute("target") == LocalPlayer.Name then
				local slash_vfx = target_ball:FindFirstChild("AeroDynamicSlashVFX")
				if slash_vfx then
					Debris:AddItem(slash_vfx, 0)
					ball_props.aerodynamic_time = tick()
				end
				local ttc = time_to_contact(target_ball, hrp)
				if ttc then
					table.insert(candidates, { ball = target_ball, ttc = ttc })
				end
			end
		end
		table.sort(candidates, function(a, b)
			return a.ttc < b.ttc
		end)

		for _, candidate in ipairs(candidates) do
			local last_fire = ball_fired_at[candidate.ball] or 0
			if (tick() - last_fire) > 1 and not holds_active() and in_round() then
				-- A4: a curving ball can cut in sharply; lead the window instead of blanket holding
				local lead = 0
				if config.curve_defense and ball_curved_for(candidate.ball) then
					lead = PARRY_WINDOW * 0.15
				end
				local window_frac = timing_frac()
				local fire_at = rtt_seconds() + PARRY_WINDOW * window_frac + lead
				if candidate.ttc <= fire_at then
					record_press(candidate.ttc)
					do_parry()
					ball_fired_at[candidate.ball] = tick()
				end
			end
		end

		-- B7: dodge cast when the swing budget is spent and a dash ability is on
		local most_urgent = candidates[1]
		if most_urgent and most_urgent.ttc < 0.35 and parry_count >= 6 then
			dodge_cast()
		end
	end

	if config.auto_spam then
		local target = current_target
		if not (target and target.PrimaryPart) then
			if config.random_target then
				pick_random_target()
			else
				select_target_by_mouse()
			end
			target = current_target
		end
		if target and target.PrimaryPart and not holds_active() then
			local ball_target = ball:GetAttribute("target")
			if ball_target and not (character:GetAttribute("Pulsed")) then
				local max_accuracy = spam_range()
				if max_accuracy > 0 then
					local ball_dist = LocalPlayer:DistanceFromCharacter(ball.Position)
					local target_dist = LocalPlayer:DistanceFromCharacter(target.PrimaryPart.Position)
					local ping_ms = Stats.Network.ServerStatsItem["Data Ping"]:GetValue()
					local fire_delay = ping_ms / 1000
					-- hub used parryCount > threshold (deadlock seed); >= threshold lets self-sustain start
					if ball_dist <= max_accuracy and parry_count >= config.spam_threshold and tick() - last_spam_fire >= fire_delay then
						last_spam_fire = tick()
						do_parry()
					end
					if ball_target == LocalPlayer.Name and target_dist > 30 and ball_dist > 30 then
						-- nothing: guard mirrored from hub, distance gate already handled in spam_range
					end
				end
			end
		end
	end

	if config.manual_spam then
		local kps = math.clamp(config.manual_kps, 1, 3000)
		if tick() - last_manual_fire >= 1 / kps then
			last_manual_fire = tick()
			do_parry()
		end
	end
end)

-- curve follow-up: second parry when an exchange lands inside personal space mid-curve
pcall(function()
	local remotes = ReplicatedStorage:FindFirstChild("Remotes", true)
	local success_all = remotes and remotes:FindFirstChild("ParrySuccessAll")
	if success_all then
		success_all.OnClientEvent:Connect(function(_, parrier)
			if not in_round() then
				return
			end
			local character = LocalPlayer.Character
			local hrp = character and character.PrimaryPart
			local ball = get_ball()
			if not (hrp and ball and current_target and current_target.PrimaryPart) then
				return
			end
			local dist_target = (hrp.Position - current_target.PrimaryPart.Position).Magnitude
			local dist_ball = (hrp.Position - ball.Position).Magnitude
			local zoomies = ball:FindFirstChild("zoomies")
			local dot = zoomies and (hrp.Position - ball.Position).Unit:Dot(zoomies.VectorVelocity.Unit) or 0
			if dist_target < 15 and dist_ball < 15 and dot > -0.25 and ball_curved() then
				do_parry()
			end
			ball_props.curving = tick()
		end)
	end
end)

workspace.Balls.ChildRemoved:Connect(function()
	parry_count = 0
	parry_active = false
	current_target = nil
	recently_picked = {}
	round_guard_until = tick() + 0.75
end)

LocalPlayer.CharacterRemoving:Connect(function()
	round_guard_until = tick() + 0.75
end)

LocalPlayer.CharacterAdded:Connect(function()
	round_guard_until = tick() + 1
end)

--// ============ anti-afk: engine-level input keepalive ============

task.spawn(function()
	pcall(function()
		while task.wait(120) do
			-- lobby-only keepalive: engine input during a live round is foreign telemetry
			if not in_round() then
				local vim = get_vim()
				if vim then
					pcall(function()
						vim:SendKeyEvent(true, Enum.KeyCode.Unknown, false, game)
						vim:SendKeyEvent(false, Enum.KeyCode.Unknown, false, game)
					end)
				end
			end
		end
	end)
end)

--// ============ anti-phantom: hold ball contact through transmission frames ============

pcall(function()
	local runtime = workspace:WaitForChild("Runtime")
	runtime.ChildAdded:Connect(function(part)
		if not config.anti_phantom then
			return
		end
		local name = part.Name:lower()
		if not (name == "maxtransmission" or name == "transmissionpart") then
			return
		end
		local character = LocalPlayer.Character
		local hrp = character and character:FindFirstChild("HumanoidRootPart")
		local ball = get_ball()
		if not (hrp and ball) then
			return
		end
		task.spawn(function()
			local started = tick()
			while tick() - started < 1 and ball.Parent do
				task.wait()
				pcall(function()
					TweenService:Create(hrp, TweenInfo.new(0.1, Enum.EasingStyle.Linear, Enum.EasingDirection.Out), { CFrame = ball.CFrame * CFrame.new(0, 0, -3) }):Play()
				end)
			end
		end)
	end)
end)

--// ============ skin changer ============
-- display-only, builder path exclusively: the equipped-sword attribute is a mirror of the
-- replicated inventory - spoofing it rebuilds nothing (verified live: attribute said
-- "Kitty Katana", character still wore Persistence Blade) and reads as an untransacted
-- equip to BAC. Swords:EquipSwordTo is the game's own local builder (Titan Blade calls
-- it mid-match), so the swap rides a sanctioned code path.

local skin_state = {
	enabled = false,
	target = nil,
	accessory = false,
	real_sword = LocalPlayer:GetAttribute("CurrentlyEquippedSword") or "Base Sword",
	reapplying = false,
}

local swords_module = nil
local function get_swords_module()
	if not swords_module then
		pcall(function()
			swords_module = require(game:GetService("ReplicatedStorage").Shared.ReplicatedInstances.Swords)
		end)
	end
	return swords_module
end

-- the animation resolver reads HasAccessoryEquipped off the equipped sword model
-- (the same _equippedSword-marked model the factory's QueryDescendants finds)
local function get_sword_model()
	local character = LocalPlayer.Character
	if not character then
		return nil
	end
	for _, child in ipairs(character:GetDescendants()) do
		if child:IsA("Model") and child:GetAttribute("_equippedSword") then
			return child
		end
	end
	return nil
end

local function apply_skin(name)
	if not name then
		return false
	end
	local character = LocalPlayer.Character
	if not character then
		return false
	end
	local swords = get_swords_module()
	if not swords then
		return false
	end
	local ok = pcall(function()
		swords:EquipSwordTo(character, name, character:GetScale(), skin_state.accessory)
	end)
	if ok then
		skin_state.target = name
	end
	return ok
end

-- verify the builder actually placed the model; escalate to the forced variant if not
local function verify_skin_path()
	task.delay(2, function()
		if not skin_state.enabled or not skin_state.target then
			return
		end
		local character = LocalPlayer.Character
		local rebuilt = false
		if character then
			for _, child in ipairs(character:GetChildren()) do
				if child:IsA("Model") and child.Name == skin_state.target then
					rebuilt = true
					break
				end
			end
		end
		if not rebuilt then
			local swords = get_swords_module()
			local target = skin_state.target
			pcall(function()
				swords:ForceEquipSwordTo(character, target, character and character:GetScale(), skin_state.accessory)
			end)
		end
	end)
end

LocalPlayer.CharacterAdded:Connect(function()
	if not skin_state.enabled or not skin_state.target then
		return
	end
	task.delay(1.5, function()
		if skin_state.enabled and skin_state.target then
			apply_skin(skin_state.target)
			verify_skin_path()
		end
	end)
end)

local function set_slash_color(color)
	-- comma float string, the same format SettingsController.RefreshSword consumes
	local value = string.format("%.6f, %.6f, %.6f", color.R, color.G, color.B)
	pcall(function()
		LocalPlayer:SetAttribute("SlashColor", value)
	end)
end

--// ============ visuals (pure reads + drawing) ============

local drawing_state = {
	segments = {},
	window_bg = nil,
	window_fill = nil,
	feed = {},
	peak_speed = 0,
}

local function init_drawing()
	for i = 1, 12 do
		local line = Drawing.new("Line")
		line.Visible = false
		line.Color = Color3.fromRGB(255, 120, 40)
		line.Thickness = 2
		drawing_state.segments[i] = line
	end
	local bg = Drawing.new("Square")
	bg.Visible = false
	bg.Filled = true
	bg.Color = Color3.fromRGB(20, 20, 20)
	bg.Transparency = 0.35
	bg.Size = Vector2.new(220, 10)
	bg.Position = Vector2.new(workspace.CurrentCamera.ViewportSize.X / 2 - 110, workspace.CurrentCamera.ViewportSize.Y - 90)
	drawing_state.window_bg = bg

	local fill = Drawing.new("Square")
	fill.Visible = false
	fill.Filled = true
	fill.Color = Color3.fromRGB(255, 120, 40)
	fill.Size = Vector2.new(0, 10)
	fill.Position = bg.Position
	drawing_state.window_fill = fill

	for i = 1, 5 do
		local text = Drawing.new("Text")
		text.Visible = false
		text.Size = 16
		text.Color = Color3.new(1, 1, 1)
		text.Outline = true
		text.Position = Vector2.new(workspace.CurrentCamera.ViewportSize.X - 360, 60 + (i - 1) * 22)
		drawing_state.feed[i] = { text = text, born = 0 }
	end
end

hooks.feed = function(line)
	local slot = drawing_state.feed[1]
	if not slot or not slot.text then
		return
	end
	for _, entry in ipairs(drawing_state.feed) do
		if entry.born < slot.born then
			slot = entry
		end
	end
	pcall(function()
		slot.text.Text = config.feed_prefix .. line
		slot.born = tick()
	end)
end

-- C10: ball path projection + parry window bar
local function draw_trajectory()
	local camera = workspace.CurrentCamera
	local ball = get_ball()
	local show = config.esp_enabled and ball ~= nil
	for i = 1, 12 do
		local segment = drawing_state.segments[i]
		if not show then
			segment.Visible = false
		else
			local zoomies = ball:FindFirstChild("zoomies")
			local velocity = zoomies and zoomies.VectorVelocity or Vector3.zero
			local t0 = (i - 1) * 0.035
			local t1 = i * 0.035
			local p0, on0 = camera:WorldToViewportPoint(ball.Position + velocity * t0)
			local p1, on1 = camera:WorldToViewportPoint(ball.Position + velocity * t1)
			segment.From = Vector2.new(p0.X, p0.Y)
			segment.To = Vector2.new(p1.X, p1.Y)
			segment.Visible = on0 and on1
		end
	end

	local bg, fill = drawing_state.window_bg, drawing_state.window_fill
	if not (config.esp_enabled and ball and LocalPlayer.Character) then
		bg.Visible = false
		fill.Visible = false
	else
		local hrp = LocalPlayer.Character.PrimaryPart
		local ttc = hrp and time_to_contact(ball, hrp) or nil
		bg.Visible = true
		fill.Visible = ttc ~= nil
		if ttc then
			local fire_at = rtt_seconds() + PARRY_WINDOW * timing_frac()
			local ratio = math.clamp(1 - ttc / math.max(fire_at * 2, 0.01), 0, 1)
			fill.Size = Vector2.new(220 * ratio, 10)
			fill.Color = ratio > 0.9 and Color3.fromRGB(80, 220, 120) or Color3.fromRGB(255, 120, 40)
		end
	end

	-- C14 feed fade
	for _, entry in ipairs(drawing_state.feed) do
		local age = tick() - entry.born
		if entry.born == 0 or age > 6 then
			entry.text.Visible = false
		else
			entry.text.Visible = config.feed_enabled
			entry.text.Transparency = math.clamp(1 - (age - 4) / 2, 0, 1)
		end
	end
end

-- C11: player billboards (ability + parries + wins)
local esp_labels = {}
local function refresh_esp()
	if not config.esp_enabled then
		for player, record in pairs(esp_labels) do
			pcall(function()
				record.billboard:Destroy()
			end)
			esp_labels[player] = nil
		end
		return
	end
	for _, player in ipairs(Players:GetPlayers()) do
		if player ~= LocalPlayer then
			local record = esp_labels[player]
			local character = player.Character
			local head = character and character:FindFirstChild("Head")
			if head and not record then
				local billboard = Instance.new("BillboardGui")
				billboard.Size = UDim2.new(0, 220, 0, 40)
				billboard.StudsOffset = Vector3.new(0, 3, 0)
				billboard.AlwaysOnTop = true
				billboard.Adornee = head
				local label = Instance.new("TextLabel")
				label.Size = UDim2.new(1, 0, 1, 0)
				label.BackgroundTransparency = 1
				label.TextColor3 = Color3.new(1, 1, 1)
				label.TextStrokeTransparency = 0.4
				label.TextSize = 12
				label.Parent = billboard
				billboard.Parent = head
				esp_labels[player] = { billboard = billboard, label = label }
				record = esp_labels[player]
			end
			if record and head then
				local ability = player:GetAttribute("CurrentlyEquippedAbility") or player:GetAttribute("EquippedAbility") or "-"
				local wins = player:GetAttribute("PlayerWins") or 0
				local parried = last_success_by_hrp[head.Parent and head.Parent.PrimaryPart] and "P" or ""
				record.label.Text = string.format("%s | %s | W %d %s", player.DisplayName, ability, wins, parried)
			elseif record and not head then
				pcall(function()
					record.billboard:Destroy()
				end)
				esp_labels[player] = nil
			end
		end
	end
end

-- C12: spectator candidates (dead players) + staff list
local function spectator_report()
	if not config.spectator_hud then
		return {}
	end
	local watching = {}
	local alive = workspace:FindFirstChild("Alive")
	local dead = workspace:FindFirstChild("Dead")
	if dead then
		for _, model in ipairs(dead:GetChildren()) do
			if Players:FindFirstChild(model.Name) and alive and not alive:FindFirstChild(model.Name) then
				table.insert(watching, model.Name)
			end
		end
	end
	return watching
end

local function check_staff()
	if config.staff_names == "" then
		return
	end
	for name in string.gmatch(config.staff_names, "[^,]+") do
		local trimmed = name:match("^%s*(.-)%s*$")
		for _, player in ipairs(Players:GetPlayers()) do
			if player.Name == trimmed or player.DisplayName == trimmed then
				if hooks.notify then
					hooks.notify("staff in server: " .. player.Name)
				end
			end
		end
	end
end

--// ============ lobby / economy ============
-- D15 is remote-class: the crate invoke is visible in the server's rate and state checks.

local CRATE_REMOTE_NAME = "RF/0f89d9363641e18e475822186e9e4ccec56271bcacae8d25eade8a38ad8db0a2" -- build 6376 pinned

local function fire_crates()
	if not config.crate_opener then
		return
	end
	local remote = ReplicatedStorage:FindFirstChild(CRATE_REMOTE_NAME, true)
	if not remote then
		return
	end
	task.spawn(function()
		for _ = 1, math.clamp(config.crate_count, 1, 50) do
			pcall(function()
				remote:InvokeServer()
			end)
			task.wait(math.max(config.crate_delay, 1))
		end
	end)
end

local function click_ui_buttons(keyword)
	local player_gui = LocalPlayer:FindFirstChild("PlayerGui")
	if not player_gui then
		return 0
	end
	local clicked = 0
	for _, gui in ipairs(player_gui:GetDescendants()) do
		if gui:IsA("TextButton") and gui.Visible and gui.Text and gui.Text:lower():find(keyword, 1, true) then
			pcall(function()
				firesignal(gui.Activated)
			end)
			clicked += 1
			if clicked >= 6 then
				break
			end
		end
	end
	return clicked
end

--// ============ UI: creep.cc ============
-- Creep's Groupbox:Resize indexes Visible/Size on every container child and throws on
-- anything unexpected, which kills the whole build task - wrap it so library bugs degrade
-- to a warning instead of a dead UI.

local function harden_groupbox(box)
	if not box or not box.Resize then
		return box
	end
	local original = box.Resize
	box.Resize = function(self, ...)
		local ok, err = pcall(original, self, ...)
		if not ok then
			warn("[kuroko] groupbox resize: " .. tostring(err))
		end
	end
	return box
end

local function harden_tab(tab)
	local original_left = tab.AddLeftGroupbox
	tab.AddLeftGroupbox = function(self, name)
		return harden_groupbox(original_left(self, name))
	end
	local original_right = tab.AddRightGroupbox
	tab.AddRightGroupbox = function(self, name)
		return harden_groupbox(original_right(self, name))
	end
	return tab
end

task.spawn(function()
	while not game:IsLoaded() do
		task.wait(0.1)
	end

	-- library: local fixed copy first (authoritative while we iterate), hosted copy second
	local LIBRARY_URL = "https://raw.githubusercontent.com/sx65/whywouldanyonelookintothisrepo/refs/heads/main/ui.lua"
	local function source_is_current(text)
		return type(text) == "string" and #text > 1000 and text:find("AddSkinGrid", 1, true) ~= nil
	end

	local library_source = nil
	pcall(function()
		local local_copy = readfile("creep_fixed.lua")
		if source_is_current(local_copy) then
			library_source = local_copy
		end
	end)
	if not library_source then
		local ok_fetch, fetched = pcall(function()
			return game:HttpGet(LIBRARY_URL)
		end)
		if ok_fetch and source_is_current(fetched) then
			library_source = fetched
		end
	end
	if not library_source then
		warn("[kuroko] UI LIBRARY IS STALE - expected build with AddSkinGrid/AddTextBox. re-upload ui.lua")
	end
	local library = assert(loadstring(library_source))()
	local window = library:CreateWindow({
		Title = "KUROKO // Blade Ball",
		Center = true,
		AutoShow = true,
		TabPadding = 8,
		MenuFadeTime = 0.2,
	})

	local function make_stub()
	local stub = {}
	local function noop()
		return stub
	end
	setmetatable(stub, {
		__index = function()
			return noop
		end,
	})
	return stub
end

-- every tab routes through this: AddTab contained, groupbox Resize hardening applied once
local original_add_tab = window.AddTab
window.AddTab = function(self, name)
	local ok, tab = pcall(original_add_tab, self, name)
	if not ok then
		warn("[kuroko] AddTab " .. tostring(name) .. ": " .. tostring(tab))
		return make_stub()
	end
	return harden_tab(tab)
end

	local tab_combat = window:AddTab("Combat")
	local tab_misc = window:AddTab("Misc")

	local parry_box = tab_combat:AddLeftGroupbox("Auto Parry")
	parry_box:AddToggle("AutoParry", {
		Text = "Auto Parry",
		Default = config.auto_parry,
		Callback = function(value)
			config.auto_parry = value
			save_config()
		end,
	})
	parry_box:AddSlider("Accuracy", {
		Text = "Parry Accuracy",
		Default = config.accuracy,
		Min = 1,
		Max = 100,
		Rounding = 0,
		Tooltip = "100 = fire at window center, reliable at any ping; lower = earlier but tighter on perfect-parry bonus",
		Callback = function(value)
			config.accuracy = value
			save_config()
		end,
	})
	parry_box:AddDropdown("CurveMethod", {
		Text = "Curve Method",
		Default = config.curve_method,
		Values = { "Camera", "Dot", "Backwards", "Slow", "Random" },
		Callback = function(value)
			config.curve_method = value
			save_config()
		end,
	})
	parry_box:AddToggle("RandomTarget", {
		Text = "Random Target",
		Default = config.random_target,
		Callback = function(value)
			config.random_target = value
			current_target = nil
			recently_picked = {}
			save_config()
		end,
	})

	local spam_box = tab_combat:AddRightGroupbox("Auto Spam")
	spam_box:AddToggle("AutoSpam", {
		Text = "Auto Spam",
		Default = config.auto_spam,
		Callback = function(value)
			config.auto_spam = value
			save_config()
		end,
	})
	spam_box:AddSlider("SpamThreshold", {
		Text = "Threshold",
		Default = config.spam_threshold,
		Min = 0,
		Max = 3,
		Rounding = 1,
		Callback = function(value)
			config.spam_threshold = value
			save_config()
		end,
	})
	spam_box:AddToggle("ManualSpam", {
		Text = "Manual Spam",
		Default = config.manual_spam,
		Callback = function(value)
			config.manual_spam = value
			save_config()
		end,
	}):AddKeyPicker("ManualSpamKey", {
		Default = "E",
		Mode = "Toggle",
		Text = "Manual Spam",
		Callback = function(value)
			config.manual_spam = value
			save_config()
		end,
	})
	spam_box:AddSlider("ManualKps", {
		Text = "Manual Spam KPS",
		Default = config.manual_kps,
		Min = 1,
		Max = 3000,
		Rounding = 0,
		Callback = function(value)
			config.manual_kps = value
			save_config()
		end,
	})

	local misc_box = tab_misc:AddLeftGroupbox("Holds & Safety")
	misc_box:AddToggle("DetHolds", {
		Text = "Ability Holds",
		Default = config.det_holds,
		Callback = function(value)
			config.det_holds = value
			save_config()
		end,
	})
	misc_box:AddToggle("AnimFix", {
		Text = "Animation Fix",
		Default = config.anim_fix,
		Callback = function(value)
			config.anim_fix = value
			save_config()
		end,
	})
	misc_box:AddToggle("AntiPhantom", {
		Text = "Anti Phantom",
		Default = config.anti_phantom,
		Tooltip = "Tweens character during phantom frames - position surface, keep off for ranked",
		Callback = function(value)
			config.anti_phantom = value
			save_config()
		end,
	})
	misc_box:AddButton("Unload", function()
		library:Unload()
	end)

	--// skins tab
	local tab_skins = window:AddTab("Skins")
	local skin_box = tab_skins:AddLeftGroupbox("Skin Changer")
	local slash_box = tab_skins:AddRightGroupbox("Slash Color")

	-- catalog: the game's own sword registry - records carry the Icon asset per skin,
-- so the grid runs static images and the preview uses the locker's live 3D renderer
	local skin_records = {}
	local seen_names = {}
	local catalog_ok, catalog_err = pcall(function()
		local sword_util = require(game:GetService("ReplicatedStorage").Common.Utils.Utilities.SwordUtil)
		local list = sword_util:GetSwordList(function()
			return true
		end)
		for _, data in pairs(list) do
			local name = data.Name
			if name and not seen_names[name] then
				seen_names[name] = true
				table.insert(skin_records, {
					name = name,
					display = data.DisplayName or name,
					icon = type(data.Icon) == "string" and data.Icon or "",
					rarity = data.Rarity or "",
					sword_type = data.SwordType or "",
					anim_type = data.AnimationType or "",
					description = data.Description or "",
				})
			end
		end
		table.sort(skin_records, function(a, b)
			return a.display < b.display
		end)
	end)
	if not catalog_ok then
		warn("[kuroko] skin catalog: " .. tostring(catalog_err))
	end

	skin_box:AddToggle("SkinChanger", {
		Text = "Skin Changer",
		Default = false,
		Callback = function(value)
			skin_state.enabled = value
			if value then
				if skin_state.target then
					apply_skin(skin_state.target)
					verify_skin_path()
				end
			elseif skin_state.real_sword then
				apply_skin(skin_state.real_sword)
			end
		end,
	})

	skin_box:AddButton("Reapply", function()
		if skin_state.target then
			apply_skin(skin_state.target)
			verify_skin_path()
		end
	end)

	skin_box:AddToggle("SkinAccessory", {
		Text = "Accessory Variant",
		Default = false,
		Callback = function(value)
			skin_state.accessory = value
			if skin_state.enabled and skin_state.target then
				apply_skin(skin_state.target)
				verify_skin_path()
			end
		end,
	})

	--// skin browser: first-class library element (AddSkinGrid), virtualized at 80 cards
	local icons_module = nil
	pcall(function()
		icons_module = require(game:GetService("ReplicatedStorage").Common.Utils.Utilities.Icons)
	end)

	local preview_model = nil
	local preview_angle = 0
	local skin_grid

	local function build_skin_browser()
		skin_grid = skin_box:AddSkinGrid({
			Text = "Skin Browser",
			Height = 470,
			MaxCards = 80,
			Items = skin_records,
			Callback = function(record)
				skin_state.target = record.name
				if skin_state.enabled then
					apply_skin(record.name)
					verify_skin_path()
				end
				skin_grid:SetMeta(
					string.format(
						"%s | %s | %s",
						record.rarity ~= "" and record.rarity or "-",
						record.sword_type ~= "" and record.sword_type or "-",
						record.anim_type ~= "" and record.anim_type or "-"
					),
					record.description
				)
				preview_model = nil
				if icons_module then
					local ok, model = pcall(function()
						return icons_module:SetSwordIconAsViewportByName(skin_grid.Preview, record.name)
					end)
					if ok then
						preview_model = model
					end
				end
			end,
		})

		RunService.RenderStepped:Connect(function(delta)
			if not preview_model then
				return
			end
			preview_angle += delta * 0.8
			pcall(function()
				local pivot = preview_model:GetPivot()
				local orbit = CFrame.Angles(0, math.rad(30), 0) * CFrame.Angles(math.rad(-12), 0, 0)
				local camera = skin_grid.Preview.CurrentCamera
				if camera then
					camera.CFrame = pivot * orbit * CFrame.new(0, 0, 5) * CFrame.Angles(0, preview_angle, 0)
				end
			end)
		end)

		for _, record in ipairs(skin_records) do
			if record.name == skin_state.real_sword then
				skin_grid.Callback(record)
				break
			end
		end
	end

	if skin_box.AddSkinGrid then
		local ok, err = pcall(build_skin_browser)
		if not ok then
			warn("[kuroko] skin browser: " .. tostring(err))
		end
	else
		warn("[kuroko] loaded library has no AddSkinGrid - stale source")
	end

	pcall(function()
		slash_box:AddLabel("Slash Color"):AddColorPicker("SlashColor", {
			Default = Color3.fromRGB(125, 125, 125),
			Callback = function(color)
				set_slash_color(color)
			end,
		})
	end)

	--// abilities tab (A1-A4, A6, B7)
	local tab_abilities = window:AddTab("Abilities")
	local cast_box = tab_abilities:AddLeftGroupbox("Auto Ability")
	local react_box = tab_abilities:AddRightGroupbox("Reactions & Tuning")

	cast_box:AddToggle("AbilityEnabled", {
		Text = "Auto Ability (Q)",
		Default = config.ability_enabled,
		Callback = function(value)
			config.ability_enabled = value
			save_config()
		end,
	})
	cast_box:AddSlider("AbilityDelay", {
		Text = "Combo Delay",
		Default = config.ability_delay,
		Min = 0,
		Max = 1,
		Rounding = 2,
		Suffix = " s",
		Callback = function(value)
			config.ability_delay = value
			save_config()
		end,
	})
	cast_box:AddSlider("AbilityCooldown", {
		Text = "Cast Cooldown",
		Default = config.ability_cooldown,
		Min = 0.5,
		Max = 5,
		Rounding = 1,
		Suffix = " s",
		Callback = function(value)
			config.ability_cooldown = value
			save_config()
		end,
	})
	cast_box:AddToggle("AbilityWhiff", {
		Text = "Cast On Enemy Whiff",
		Default = config.ability_whiff,
		Callback = function(value)
			config.ability_whiff = value
			save_config()
		end,
	})
	cast_box:AddToggle("AbilityDodge", {
		Text = "Dodge Cast (dash abilities)",
		Default = config.ability_dodge,
		Callback = function(value)
			config.ability_dodge = value
			save_config()
		end,
	})

	react_box:AddToggle("ReactionPull", {
		Text = "Counter-Cast On Pull",
		Default = config.reaction_pull,
		Callback = function(value)
			config.reaction_pull = value
			save_config()
		end,
	})
	react_box:AddToggle("ReactionStance", {
		Text = "Counter-Cast After Stance",
		Default = config.reaction_stance,
		Callback = function(value)
			config.reaction_stance = value
			save_config()
		end,
	})
	react_box:AddToggle("Calibrator", {
		Text = "Perfect-Parry Calibrator",
		Default = config.calibrator,
		Tooltip = "Closed-loop window tuning from parry echo timing",
		Callback = function(value)
			config.calibrator = value
			save_config()
		end,
	})
	react_box:AddToggle("CurveDefense", {
		Text = "Curve Defense",
		Default = config.curve_defense,
		Callback = function(value)
			config.curve_defense = value
			save_config()
		end,
	})
	react_box:AddToggle("AutoCurvePick", {
		Text = "Auto Curve Pick",
		Default = config.auto_curve_pick,
		Callback = function(value)
			config.auto_curve_pick = value
			save_config()
		end,
	})
	react_box:AddToggle("AutoEmote", {
		Text = "Emote On Kill",
		Default = config.auto_emote,
		Callback = function(value)
			config.auto_emote = value
			save_config()
		end,
	})

	--// visuals tab (C10-C14)
	local tab_visuals = window:AddTab("Visuals")
	local esp_box = tab_visuals:AddLeftGroupbox("ESP & HUD")
	local staff_box = tab_visuals:AddRightGroupbox("Awareness")

	esp_box:AddToggle("EspEnabled", {
		Text = "Trajectory + Window Bar",
		Default = config.esp_enabled,
		Callback = function(value)
			config.esp_enabled = value
			save_config()
		end,
	})
	esp_box:AddToggle("FeedEnabled", {
		Text = "Kill Feed",
		Default = config.feed_enabled,
		Callback = function(value)
			config.feed_enabled = value
			save_config()
		end,
	})
	staff_box:AddToggle("SpectatorHud", {
		Text = "Spectator Report",
		Default = config.spectator_hud,
		Callback = function(value)
			config.spectator_hud = value
			save_config()
		end,
	})
	if staff_box.AddTextBox then
		staff_box:AddTextBox("StaffNames", {
			Text = "Staff names (csv)",
			Default = config.staff_names,
			Placeholder = "name1,name2",
			Callback = function(value)
				config.staff_names = value or ""
				save_config()
				check_staff()
			end,
		})
	else
		warn("[kuroko] loaded library has no AddTextBox - stale source")
	end
	staff_box:AddButton("Check Staff Now", check_staff)

	--// lobby tab (D15-D18)
	local tab_lobby = window:AddTab("Lobby")
	local eco_box = tab_lobby:AddLeftGroupbox("Economy")
	local stats_box = tab_lobby:AddRightGroupbox("Stats")

	eco_box:AddToggle("CrateOpener", {
		Text = "Auto Open Crates",
		Default = config.crate_opener,
		Tooltip = "Remote-class: the invoke is visible to server rate/state checks",
		Callback = function(value)
			config.crate_opener = value
			save_config()
		end,
	})
	eco_box:AddSlider("CrateCount", {
		Text = "Crates Per Run",
		Default = config.crate_count,
		Min = 1,
		Max = 50,
		Rounding = 0,
		Callback = function(value)
			config.crate_count = value
			save_config()
		end,
	})
	eco_box:AddSlider("CrateDelay", {
		Text = "Delay Between Opens",
		Default = config.crate_delay,
		Min = 1,
		Max = 10,
		Rounding = 0,
		Suffix = " s",
		Callback = function(value)
			config.crate_delay = value
			save_config()
		end,
	})
	eco_box:AddButton("Open Crates Now", fire_crates)
	eco_box:AddToggle("AutoClaim", {
		Text = "Auto Claim Rewards",
		Default = config.auto_claim,
		Callback = function(value)
			config.auto_claim = value
			save_config()
		end,
	})
	eco_box:AddToggle("AutoSpin", {
		Text = "Auto Spin Wheel",
		Default = config.auto_spin,
		Callback = function(value)
			config.auto_spin = value
			save_config()
		end,
	})

	local stat_lines = {}
	for i = 1, 6 do
		stat_lines[i] = stats_box:AddLabel("-")
	end

	misc_box:AddToggle("MoveOptimizer", {
		Text = "Movement Optimizer",
		Default = config.move_optimizer,
		Tooltip = "Move intent away from the ball's approach; hands off inside the parry window",
		Callback = function(value)
			config.move_optimizer = value
			save_config()
		end,
	})

	--// runtime
	hooks.notify = function(message)
		library:Notify(message)
	end
	pcall(init_drawing)
	pcall(function()
		RunService.RenderStepped:Connect(function()
			pcall(draw_trajectory)
		end)
	end)
	task.spawn(function()
		while task.wait(0.5) do
			pcall(refresh_esp)
			local lp = LocalPlayer
			local ok, stats_text = pcall(function()
				return {
					string.format("parry accuracy: %d%% (%d presses)", math.floor((press_stats.hits / math.max(press_stats.total, 1)) * 100), press_stats.total),
					string.format("timing bias: %+.2f", press_stats.bias),
					string.format("wins: %d  elims: %d", lp:GetAttribute("PlayerWins") or 0, lp:GetAttribute("PlayerElims") or 0),
					string.format("total RAP: %d", lp:GetAttribute("TotalRAP") or 0),
					string.format("ability: %s", tostring(lp:GetAttribute("CurrentlyEquippedAbility") or "-")),
					string.format("path: %s", bac.path),
				}
			end)
			if ok then
				for i, line in ipairs(stats_text) do
					if stat_lines[i] then
						pcall(function()
							stat_lines[i]:SetText(line)
						end)
					end
				end
			end
		end
	end)
	task.spawn(function()
		while task.wait(2) do
			if config.auto_claim then
				click_ui_buttons("claim")
			end
			if config.auto_spin then
				click_ui_buttons("spin")
			end
		end
	end)
	task.spawn(function()
		while task.wait(30) do
			pcall(check_staff)
		end
	end)
	pcall(check_staff)

	pcall(function()
		library:SetWatermarkVisibility(true)
	end)
	local watermark_clock = 0
	RunService.Heartbeat:Connect(function()
		if tick() - watermark_clock < 0.25 then
			return
		end
		watermark_clock = tick()
		local ball = get_ball()
		local zoomies = ball and ball:FindFirstChild("zoomies")
		local speed = zoomies and math.floor(zoomies.VectorVelocity.Magnitude) or 0
		if speed > drawing_state.peak_speed then
			drawing_state.peak_speed = speed
		end
		local spectators = spectator_report()
		pcall(function()
			library:SetWatermark(("KUROKO | %s | ball %d (peak %d) | parries %d | acc %d%% | bias %+.2f | spec %d"):format(
				bac.path,
				speed,
				drawing_state.peak_speed,
				parry_count,
				math.floor((press_stats.hits / math.max(press_stats.total, 1)) * 100),
				press_stats.bias,
				#spectators
			))
		end)
	end)

	library:Notify("KUROKO loaded - parry path: " .. bac.path)
end)

return nil

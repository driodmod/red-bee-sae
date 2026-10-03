do
    getgenv().AutoGKV2Config = getgenv().AutoGKV2Config or { enabled = false }
    getgenv().AutoGroundSaveConfig = getgenv().AutoGroundSaveConfig or { enabled = false }
    getgenv().AutoGKConfig = getgenv().AutoGKConfig or {
        enabled = false,
        diveSpeed = 10,
    }
    if not getgenv().AutoGKConfig.diveSpeed then getgenv().AutoGKConfig.diveSpeed = 10 end
    getgenv().TouchReachConfig = getgenv().TouchReachConfig or {
        enabled = false, reach = 4.0, spoofTarget = 3.9,
        antiCancel = true, protectBall = true, instantSteal = true, naturalSpoof = true,
        blockDeny = true, visualizer = false,
    }
    local cfg = getgenv().TouchReachConfig
    cfg.reach = tonumber(cfg.reach) or 4.0
    if cfg.reach == math.huge or cfg.reach <= 0 then cfg.reach = 4.0 end
    cfg.reach = math.clamp(cfg.reach, 1, 60)
    cfg.spoofTarget = math.clamp(cfg.spoofTarget or 3.9, 1, 3.97)

    local newcclosure_fn = newcclosure or function(f) return f end
    local checkcaller_fn = checkcaller
    local getrawmetatable_fn = getrawmetatable
    local setreadonly_fn = setreadonly
    local getgc_fn = getgc
    local islclosure_fn = islclosure
    local getnamecallmethod_fn = getnamecallmethod
    local getconnections_fn = getconnections
    local hookfunction_fn = hookfunction

    if getgenv()._UR_Connections then
        for _, cc in pairs(getgenv()._UR_Connections) do
            pcall(function() cc:Disconnect() end)
        end
    end
    getgenv()._UR_Connections = {}
    local conns = getgenv()._UR_Connections
    getgenv()._UR_LoopID = (getgenv()._UR_LoopID or 0) + 1
    local currentLoopID = getgenv()._UR_LoopID

    local GOAL_A_X, GOAL_B_X = -313.13, -115.936
    local Z_MIN, Z_MAX = 78.036, 107.715
    local GOAL_CENTER_Z = (Z_MIN + Z_MAX) / 2
    local GRAVITY = 55
    local GROUND_Y = 5.473
    local BOUNCE_DAMP_Y = 0.55
    local CROSSBAR_Y = 18
    local SIM_DT = 0.005
    local MAX_STEPS = 2000
    local THREAT_WINDOW = 7.5
    local GOAL_OFFSET = -0.5
    local Z_SAVE_MIN = Z_MIN - 2.6
    local Z_SAVE_MAX = Z_MAX + 2.6
    local Y_SAVE_MAX = CROSSBAR_Y + 0.6
    local STAND_REACH_Y = GROUND_Y + 5.5
    local GK_Settings = { AntiPhase = false }
    local smoothVelocity = Vector3.zero
    local getcallingscript = getcallingscript or function() return nil end

    pcall(function()
        local oldTick
        oldTick = hookfunction(tick, function(...)
            if GK_Settings.AntiPhase then
                local caller = getcallingscript()
                if caller and caller.Name == "BallHandler" then return oldTick(...) * 0.6 end
                local ok, src = pcall(debug.info, 2, "s")
                if ok and src and string.find(src, "BallHandler") then return oldTick(...) * 0.6 end
            end
            return oldTick(...)
        end)
    end)

    local function SimulateExactGamePhysics(ballPos, ballVel, ballRotVel, goalLineX)
        if math.abs(ballVel.X) < 0.2 then return nil end
        if (ballVel.X < 0) ~= (goalLineX < ballPos.X) then return nil end
        local totalTime, bounces = 0, 0
        local flightTime = 0
        local sPx, sPy, sPz = ballPos.X, ballPos.Y, ballPos.Z
        local sVx, sVy, sVz = ballVel.X, ballVel.Y, ballVel.Z
        local curveFactor = ballRotVel.Y / -45
        local prevX, prevY, prevZ = sPx, sPy, sPz
        local trajectory = {}
        table.insert(trajectory, {x=sPx, y=sPy, z=sPz, t=0, vy=sVy, b=0})
        local crossedGoal = false
        for _ = 1, MAX_STEPS do
            flightTime = flightTime + SIM_DT
            totalTime = totalTime + SIM_DT
            local angle = curveFactor * flightTime
            local curVx = sVx * math.cos(angle) - sVz * math.sin(angle)
            local curVz = sVx * math.sin(angle) + sVz * math.cos(angle)
            local npx = sPx + sVx * flightTime + 0.5 * (curVx - sVx) * flightTime
            local npy = sPy + sVy * flightTime - 0.5 * GRAVITY * (flightTime^2)
            local npz = sPz + sVz * flightTime + 0.5 * (curVz - sVz) * flightTime
            local nvy = sVy - GRAVITY * flightTime
            table.insert(trajectory, {x=npx, y=npy, z=npz, t=totalTime, vy=nvy, b=bounces})
            if (prevX <= goalLineX and npx >= goalLineX) or (prevX >= goalLineX and npx <= goalLineX) then
                crossedGoal = true
                break
            end
            if npy < GROUND_Y then
                bounces = bounces + 1
                local dampXZ = math.abs(nvy) < 10 and 0.99 or 0.80
                sVx, sVz = curVx * dampXZ, curVz * dampXZ
                sVy = math.abs(nvy) * BOUNCE_DAMP_Y
                sPx, sPy, sPz = npx, GROUND_Y, npz
                local rotImpact = (Vector3.new(0, 1, 0)):Cross(Vector3.new(curVx, 0, curVz).Unit).Unit * (math.sqrt(curVx^2 + curVz^2) * 0.8 / 1.5)
                curveFactor = (rotImpact.Y + (curveFactor * -45 * 0.8)) / -45
                flightTime = 0
                npx, npy, npz = sPx, sPy, sPz
            end
            prevX, prevY, prevZ = npx, npy, npz
            if (curVx^2 + nvy^2 + curVz^2) < 0.09 or totalTime > THREAT_WINDOW then break end
        end
        return crossedGoal and trajectory or nil
    end

    local function GetStateAtX(trajectory, targetX)
        if not trajectory or #trajectory == 0 then return nil end
        local prev = trajectory[1]
        for i = 2, #trajectory do
            local cur = trajectory[i]
            if (prev.x <= targetX and cur.x >= targetX) or (prev.x >= targetX and cur.x <= targetX) then
                local frac = math.abs(targetX - prev.x) / math.max(math.abs(cur.x - prev.x), 0.0001)
                return {
                    x = targetX,
                    y = math.max(prev.y + (cur.y - prev.y) * frac, GROUND_Y),
                    z = prev.z + (cur.z - prev.z) * frac,
                    t = prev.t + (cur.t - prev.t) * frac,
                    vy = prev.vy + (cur.vy - prev.vy) * frac,
                    b = cur.b
                }
            end
            prev = cur
        end
        return nil
    end

    local cachedBall = nil
    local function GetBall()
        if not cachedBall or not cachedBall:IsDescendantOf(workspace) then
            local f = workspace:FindFirstChild("FootballField")
            cachedBall = f and f:FindFirstChild("SoccerBall")
        end
        return cachedBall
    end

    local function lerpV3(a, b, t) return a + (b - a) * t end

    RunService.Heartbeat:Connect(function()
        if not getgenv().AutoGKConfig.enabled and not getgenv().AutoGroundSaveConfig.enabled then return end
        local char = player.Character
        local hrp = char and char:FindFirstChild("HumanoidRootPart")
        local hum = char and char:FindFirstChild("Humanoid")
        local ball = GetBall()
        if not hrp or not hum then
            if hrp and hrp:FindFirstChild("GK_V") then
                hrp.GK_V.Enabled = false
                hrp.GK_R.Enabled = false
                hum.AutoRotate = true
            end
            return
        end
        if not hrp:FindFirstChild("GK_V") then
            local att = Instance.new("Attachment", hrp); att.Name = "GK_A"
            local lvI = Instance.new("LinearVelocity", hrp); lvI.Name = "GK_V"; lvI.Attachment0 = att
            lvI.VelocityConstraintMode = Enum.VelocityConstraintMode.Vector; lvI.ForceLimitMode = Enum.ForceLimitMode.PerAxis
            local aoI = Instance.new("AlignOrientation", hrp); aoI.Name = "GK_R"; aoI.Attachment0 = att
            aoI.Mode = Enum.OrientationAlignmentMode.OneAttachment; aoI.MaxTorque = math.huge; aoI.Responsiveness = 40
        end
        local lv, ao = hrp.GK_V, hrp.GK_R
        if not ball then
            lv.Enabled = false
            ao.Enabled = false
            hum.AutoRotate = true
            return
        end
        local rawGoalX = (math.abs(hrp.Position.X - GOAL_A_X) < math.abs(hrp.Position.X - GOAL_B_X)) and GOAL_A_X or GOAL_B_X
        local dir = (rawGoalX < -200) and 1 or -1
        local goalX = rawGoalX + (GOAL_OFFSET * dir)
        local ballPos = ball.Position
        local vel = ball.AssemblyLinearVelocity
        local rotVel = ball.AssemblyAngularVelocity
        local isShotOnTarget, timeToGoal = false, 999
        local targetZ, predY = GOAL_CENTER_Z, GROUND_Y
        local targetX = goalX + dir * 0.5
        local ballHeading = ((rawGoalX == GOAL_A_X) and vel.X < 0) or ((rawGoalX == GOAL_B_X) and vel.X > 0)
        local ballBehind = (dir == 1 and ballPos.X < hrp.Position.X) or (dir == -1 and ballPos.X > hrp.Position.X)
        local trajectory = nil
        if ballHeading and not ballBehind then
            trajectory = SimulateExactGamePhysics(ballPos, vel, rotVel, rawGoalX)
        end
        local goalState = trajectory and GetStateAtX(trajectory, rawGoalX) or nil
        if goalState and goalState.t < THREAT_WINDOW then
            timeToGoal = goalState.t
            if goalState.z >= Z_SAVE_MIN and goalState.z <= Z_SAVE_MAX and goalState.y <= Y_SAVE_MAX then
                isShotOnTarget = true
                targetZ = goalState.z
                predY = goalState.y
            end
        end
        local isActivelySaving = isShotOnTarget and timeToGoal <= 1.6
        if not isActivelySaving then
            lv.Enabled = false
            ao.Enabled = false
            hum.AutoRotate = true
            smoothVelocity = Vector3.zero
            return
        end
        local st = hum:GetState()
        local onGround = st ~= Enum.HumanoidStateType.Jumping and st ~= Enum.HumanoidStateType.Freefall
        if onGround and getgenv().AutoGKConfig.enabled and predY >= STAND_REACH_Y and timeToGoal <= 0.6 then
            hum.Jump = true
            hum:ChangeState(Enum.HumanoidStateType.Jumping)
        end
        local canGroundSave = getgenv().AutoGroundSaveConfig.enabled and onGround
        local canDive = getgenv().AutoGKConfig.enabled and not onGround
        if not canGroundSave and not canDive then
            lv.Enabled = false
            ao.Enabled = false
            hum.AutoRotate = true
            smoothVelocity = Vector3.zero
            return
        end
        if canGroundSave then hum.WalkSpeed = 23 end
        lv.Enabled = true
        ao.Enabled = true
        hum.AutoRotate = false
        lv.MaxAxesForce = Vector3.new(5000000, 0, 5000000)
        local lungeVec = Vector3.new(targetX, hrp.Position.Y, targetZ) - hrp.Position
        local desiredVel = Vector3.zero
        if lungeVec.Magnitude > 0.05 then
            desiredVel = lungeVec * 40
            if desiredVel.Magnitude > getgenv().AutoGKConfig.diveSpeed then
                desiredVel = desiredVel.Unit * getgenv().AutoGKConfig.diveSpeed
            end
        end
        smoothVelocity = lerpV3(smoothVelocity, desiredVel, 1.0)
        lv.VectorVelocity = smoothVelocity
        local lookDir = Vector3.new(ballPos.X, hrp.Position.Y, ballPos.Z) - hrp.Position
        if lookDir.Magnitude > 0.1 then
            ao.CFrame = CFrame.lookAt(hrp.Position, hrp.Position + lookDir.Unit * 10)
        end
    end)

    local state = {
        FAKE_DIST = 3.2, cachedBall = nil, ballAlive = false, partMode = {}, limbPriority = {},
        kickBallRemote = nil, blockedRemotes = {}, cacheDirty = true, lastCharModel = nil,
    }
    local BANISH_VEC = Vector3.new(0, 9e8, 0)
    local HITBOXES = {
        ["UpperTorso"] = 0.4, ["RightFoot"] = 0.3, ["LeftFoot"] = 0.3,
        ["RightLowerLeg"] = 0.2, ["LeftLowerLeg"] = 0.2, ["RightUpperLeg"] = 0.2,
        ["LeftUpperLeg"] = 0.2, ["HumanoidRootPart"] = 0.1, ["Torso"] = 0.4,
        ["Right Leg"] = 0.3, ["Left Leg"] = 0.3,
    }
    local BALL_NAMES = { "SoccerBall", "Ball", "Football" }
    local SAFE_REMOTE_NAMES = {
        ["KickBall"] = true, ["DropBallEvent"] = true, ["RemoveBallEvent"] = true,
        ["BallPositionEvent"] = true, ["KickBallEvent"] = true, ["MeasureLag"] = true,
        ["MeasureLagEvent"] = true, ["GoalEvent"] = true, ["NearGoalEvent"] = true,
    }

    local function findBall()
        local field = workspace:FindFirstChild("FootballField")
        if field then
            for _, name in ipairs(BALL_NAMES) do
                local b = field:FindFirstChild(name)
                if b then
                    if b:IsA("BasePart") then return b end
                    if b:IsA("Model") then return b.PrimaryPart or b:FindFirstChildWhichIsA("BasePart") end
                end
            end
        end
        for _, name in ipairs(BALL_NAMES) do
            local b = workspace:FindFirstChild(name)
            if b then
                if b:IsA("BasePart") then return b end
                if b:IsA("Model") then return b.PrimaryPart or b:FindFirstChildWhichIsA("BasePart") end
            end
        end
        return nil
    end

    local function validateBall()
        if not state.cachedBall then return false end
        local ok, result = pcall(function() return state.cachedBall:IsDescendantOf(game) end)
        return ok and result == true
    end

    local function refreshCache()
        if validateBall() then
            state.ballAlive = true
        else
            state.cachedBall = findBall()
            state.ballAlive = (state.cachedBall ~= nil)
        end
        if not state.kickBallRemote then
            local r = ReplicatedStorage:FindFirstChild("KickBall")
            if r and (r:IsA("RemoteEvent") or r:IsA("RemoteFunction")) then
                state.kickBallRemote = r
            end
        end
        local char = player.Character
        if char ~= state.lastCharModel then
            state.lastCharModel = char
            for k in pairs(state.partMode) do state.partMode[k] = nil end
            for k in pairs(state.limbPriority) do state.limbPriority[k] = nil end
            if char then
                for name, prio in pairs(HITBOXES) do
                    local part = char:FindFirstChild(name)
                    if part and part:IsA("BasePart") then
                        state.partMode[part] = 1
                        state.limbPriority[part] = prio
                    end
                end
            end
            for _, p in pairs(Players:GetPlayers()) do
                if p ~= player and p.Character then
                    local hrp = p.Character:FindFirstChild("HumanoidRootPart")
                    if hrp and hrp:IsA("BasePart") then
                        state.partMode[hrp] = 2
                    end
                end
            end
        end
        state.cacheDirty = false
    end

    local hbTimer = 0
    table.insert(conns, RunService.Heartbeat:Connect(function(dt)
        if state.ballAlive then
            if not validateBall() then
                state.ballAlive = false
                state.cacheDirty = true
            end
        end
        hbTimer = hbTimer + dt
        if state.cacheDirty and hbTimer >= 0.3 then
            hbTimer = 0
            pcall(refreshCache)
        elseif hbTimer >= 3 then
            hbTimer = 0
            state.cacheDirty = true
        end
    end))

    local function onBallChildAdded(child)
        for _, name in ipairs(BALL_NAMES) do
            if child.Name == name then
                if child:IsA("BasePart") then
                    state.cachedBall = child
                    state.ballAlive = true
                    return
                elseif child:IsA("Model") then
                    state.cachedBall = child.PrimaryPart or child:FindFirstChildWhichIsA("BasePart")
                    state.ballAlive = (state.cachedBall ~= nil)
                    return
                end
            end
        end
    end

    task.spawn(function()
        local field = workspace:FindFirstChild("FootballField")
        if not field then field = workspace:WaitForChild("FootballField", 30) end
        if field then
            table.insert(conns, field.ChildAdded:Connect(function(child) onBallChildAdded(child) end))
            for _, name in ipairs(BALL_NAMES) do
                local b = field:FindFirstChild(name)
                if b then
                    if b:IsA("BasePart") then
                        state.cachedBall = b
                        state.ballAlive = true
                    elseif b:IsA("Model") then
                        state.cachedBall = b.PrimaryPart or b:FindFirstChildWhichIsA("BasePart")
                        state.ballAlive = (state.cachedBall ~= nil)
                    end
                    break
                end
            end
        end
    end)

    table.insert(conns, workspace.ChildAdded:Connect(function(child)
        for _, name in ipairs(BALL_NAMES) do
            if child.Name == name then
                onBallChildAdded(child)
                return
            end
        end
        if child.Name == "FootballField" then
            state.cacheDirty = true
            task.spawn(function()
                table.insert(conns, child.ChildAdded:Connect(function(cc) onBallChildAdded(cc) end))
            end)
        end
    end))

    table.insert(conns, Players.PlayerAdded:Connect(function() state.cacheDirty = true end))
    table.insert(conns, Players.PlayerRemoving:Connect(function() state.cacheDirty = true end))

    task.spawn(function()
        while task.wait(2) do
            if getgenv()._UR_LoopID ~= currentLoopID then break end
            local ping = 0
            pcall(function() ping = player:GetNetworkPing() end)
            local base = math.clamp(3.50 - (ping * 1.5), 2.80, 3.50)
            state.FAKE_DIST = base
        end
    end)

    local cancelBlockCount = 0
    local DENIED_SUBSTRINGS = { "denied", "cancel", "blocked", "reject", "refuse", "failed" }
    local DENIED_EVENT_NAMES = {
        "KickBallDeniedEvent", "KickBallDenied", "KickDenied", "TouchDenied", "KickCancel", "CancelKick", "KickBlocked", "BallDenied", "KickFailed", "OnKickDenied", "KickCancelled", "KickRefused", "DenyKick", "RejectKick", "KickRejected", "BallTouchDenied", "TouchCancelled", "TouchBlocked", "OnDenyKick", "ServerDenyKick", "CancelTouch",
    }

    local function nameIsDenied(name)
        local lower = name:lower()
        for _, s in ipairs(DENIED_SUBSTRINGS) do
            if lower:find(s, 1, true) then return true end
        end
        for _, exact in ipairs(DENIED_EVENT_NAMES) do
            if name == exact then return true end
        end
        return false
    end

    local function blockDeniedEvent(ev)
        if not ev or not ev:IsA("RemoteEvent") then return end
        if state.blockedRemotes[ev] then return end
        state.blockedRemotes[ev] = true
        if getconnections_fn then
            pcall(function()
                for _, cc in pairs(getconnections_fn(ev.OnClientEvent)) do
                    pcall(function() cc:Disable() end)
                end
            end)
        end
    end

    local function blockAllDeniedEvents()
        for _, child in pairs(ReplicatedStorage:GetChildren()) do
            if not SAFE_REMOTE_NAMES[child.Name] and child:IsA("RemoteEvent") and nameIsDenied(child.Name) then
                blockDeniedEvent(child)
            end
        end
    end

    task.delay(1, function() if getgenv()._UR_LoopID == currentLoopID then pcall(blockAllDeniedEvents) end end)
    task.delay(5, function() if getgenv()._UR_LoopID == currentLoopID then pcall(blockAllDeniedEvents) end end)

    table.insert(conns, ReplicatedStorage.ChildAdded:Connect(function(child)
        if not cfg.blockDeny then return end
        if not SAFE_REMOTE_NAMES[child.Name] and child:IsA("RemoteEvent") and nameIsDenied(child.Name) then
            task.defer(function() pcall(blockDeniedEvent, child) end)
        end
    end))

    if not getgenv()._V22MetaHooked then
        local hookOK = false
        pcall(function()
            if not getrawmetatable_fn or not setreadonly_fn then return end
            local mt = getrawmetatable_fn(game)
            local oldIndex = mt.__index
            local oldNamecall = mt.__namecall
            setreadonly_fn(mt, false)
            mt.__index = newcclosure_fn(function(self, key)
                if key ~= "Position" then return oldIndex(self, key) end
                if not cfg.enabled then return oldIndex(self, key) end
                if checkcaller_fn and checkcaller_fn() then return oldIndex(self, key) end
                if not state.ballAlive then return oldIndex(self, key) end
                local mode = state.partMode[self]
                if not mode then return oldIndex(self, key) end
                if mode == 2 then return BANISH_VEC end
                local ok, result = pcall(function()
                    local realPos = oldIndex(self, "Position")
                    local ball = state.cachedBall
                    if not ball then return realPos end
                    local ballPos = oldIndex(ball, "Position")
                    if not ballPos then return realPos end
                    local dX = ballPos.X - realPos.X
                    local dY = ballPos.Y - realPos.Y
                    local dZ = ballPos.Z - realPos.Z
                    local distSq = dX * dX + dY * dY + dZ * dZ
                    local fakeDist = state.FAKE_DIST
                    if distSq <= fakeDist * fakeDist then return realPos end
                    local reachDist = cfg.reach
                    if distSq > reachDist * reachDist then return realPos end
                    local dist = math.sqrt(distSq)
                    if dist < 0.01 then return realPos end
                    local priorityOffset = state.limbPriority[self] or 0
                    local targetSpoofDist = math.max(0.5, fakeDist - priorityOffset)
                    local invDist = 1 / dist
                    return Vector3.new(
                        ballPos.X - dX * invDist * targetSpoofDist,
                        ballPos.Y - dY * invDist * targetSpoofDist,
                        ballPos.Z - dZ * invDist * targetSpoofDist
                    )
                end)
                return ok and result or oldIndex(self, key)
            end)
            mt.__namecall = newcclosure_fn(function(self, ...)
                if not getnamecallmethod_fn then return oldNamecall(self, ...) end
                local method = getnamecallmethod_fn()
                if cfg.enabled and state.kickBallRemote and self == state.kickBallRemote and method == "FireServer" then
                    local args = { ... }
                    if type(args[4]) == "number" then args[4] = state.FAKE_DIST end
                    return oldNamecall(self, table.unpack(args))
                end
                if cfg.blockDeny and (method == "FireServer" or method == "InvokeServer") then
                    local t = typeof(self)
                    if t == "Instance" then
                        local isSafe = false
                        local isDenied = false
                        pcall(function()
                            isSafe = SAFE_REMOTE_NAMES[self.Name] or false
                            if not isSafe then isDenied = nameIsDenied(self.Name) end
                        end)
                        if not isSafe and isDenied then
                            cancelBlockCount = cancelBlockCount + 1
                            return
                        end
                    end
                end
                return oldNamecall(self, ...)
            end)
            setreadonly_fn(mt, true)
            hookOK = true
        end)
        if hookOK then getgenv()._V22MetaHooked = true end
    end

    local hookedFuncs = {}
    local GC_HOOK_NAMES = {
        ["getClosestPlayerName"] = "closest",
        ["onBallPositionEvent"] = "ballpos",
        ["onKickDenied"] = "cancel",
        ["showCancelled"] = "cancel",
        ["cancelKick"] = "cancel",
        ["onKickCancelled"] = "cancel",
        ["kickDenied"] = "cancel",
        ["kickCancelled"] = "cancel",
        ["kickBlocked"] = "cancel",
        ["handleDenied"] = "cancel",
        ["handleCancel"] = "cancel",
    }

    local function tryHookFunctions()
        if not getgc_fn or not islclosure_fn or not hookfunction_fn then return end
        local ok, list = pcall(getgc_fn, true)
        if not ok then return end
        for _, v in pairs(list) do
            if type(v) == "function" and islclosure_fn(v) and not hookedFuncs[v] then
                local funcName = nil
                pcall(function()
                    local info = debug.getinfo(v)
                    if info then pcall(function() funcName = info.name end) end
                end)
                if funcName then
                    local hookType = GC_HOOK_NAMES[funcName]
                    if hookType == "closest" then
                        local orig
                        local hOK, hOrig = pcall(hookfunction_fn, v, newcclosure_fn(function(...)
                            if cfg.enabled and cfg.blockDeny then return player.Name end
                            return orig(...)
                        end))
                        if hOK and hOrig then orig = hOrig; hookedFuncs[v] = true end
                    elseif hookType == "ballpos" then
                        local orig
                        local hOK, hOrig = pcall(hookfunction_fn, v, newcclosure_fn(function(lag, names, positions, ...)
                            if cfg.enabled and cfg.blockDeny and type(names) == "table" and type(positions) == "table" then
                                for i, name in pairs(names) do
                                    if name ~= player.Name then positions[i] = BANISH_VEC end
                                end
                            end
                            return orig(lag, names, positions, ...)
                        end))
                        if hOK and hOrig then orig = hOrig; hookedFuncs[v] = true end
                    elseif hookType == "cancel" then
                        local orig
                        local hOK, hOrig = pcall(hookfunction_fn, v, newcclosure_fn(function(...)
                            if cfg.enabled and cfg.blockDeny then
                                cancelBlockCount = cancelBlockCount + 1
                                return
                            end
                            return orig(...)
                        end))
                        if hOK and hOrig then orig = hOrig; hookedFuncs[v] = true end
                    end
                end
            end
        end
    end

    task.spawn(function()
        tryHookFunctions()
        task.wait(2)
        tryHookFunctions()
    end)

    getgenv()._AutoGKV2Cleanup = function()
        getgenv().AutoGKV2Config.enabled = false
        getgenv().AutoGroundSaveConfig.enabled = false
        getgenv().AutoGKConfig.enabled = false
        cfg.enabled = false
        local charNode = player.Character
        if charNode then
            local hrp = charNode:FindFirstChild("HumanoidRootPart")
            if hrp then
                local v = hrp:FindFirstChild("GK_V")
                local r = hrp:FindFirstChild("GK_R")
                local a = hrp:FindFirstChild("GK_A")
                if v then v:Destroy() end
                if r then r:Destroy() end
                if a then a:Destroy() end
            end
            local hum = charNode:FindFirstChildOfClass("Humanoid")
            if hum then hum.AutoRotate = true end
        end
    end
end
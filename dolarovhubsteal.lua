

local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 21) then
					if (Enum <= 10) then
						if (Enum <= 4) then
							if (Enum <= 1) then
								if (Enum > 0) then
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									local T = Stk[A];
									for Idx = A + 1, Inst[3] do
										Insert(T, Stk[Idx]);
									end
								end
							elseif (Enum <= 2) then
								Stk[Inst[2]]();
							elseif (Enum > 3) then
								Stk[Inst[2]] = Env[Inst[3]];
							else
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 7) then
							if (Enum <= 5) then
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 6) then
								Stk[Inst[2]] = Inst[3];
							else
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							end
						elseif (Enum <= 8) then
							Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
						elseif (Enum > 9) then
							local A = Inst[2];
							Stk[A](Stk[A + 1]);
						else
							local A = Inst[2];
							local T = Stk[A];
							local B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						end
					elseif (Enum <= 15) then
						if (Enum <= 12) then
							if (Enum > 11) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							end
						elseif (Enum <= 13) then
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						elseif (Enum > 14) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						end
					elseif (Enum <= 18) then
						if (Enum <= 16) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						elseif (Enum == 17) then
							local B;
							local A;
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
						else
							local T;
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							T = Stk[A];
							B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						end
					elseif (Enum <= 19) then
						local NewProto = Proto[Inst[3]];
						local NewUvals;
						local Indexes = {};
						NewUvals = Setmetatable({}, {__index=function(_, Key)
							local Val = Indexes[Key];
							return Val[1][Val[2]];
						end,__newindex=function(_, Key, Value)
							local Val = Indexes[Key];
							Val[1][Val[2]] = Value;
						end});
						for Idx = 1, Inst[4] do
							VIP = VIP + 1;
							local Mvm = Instr[VIP];
							if (Mvm[1] == 43) then
								Indexes[Idx - 1] = {Stk,Mvm[3]};
							else
								Indexes[Idx - 1] = {Upvalues,Mvm[3]};
							end
							Lupvals[#Lupvals + 1] = Indexes;
						end
						Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
					elseif (Enum > 20) then
						Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
					else
						local B;
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
					end
				elseif (Enum <= 32) then
					if (Enum <= 26) then
						if (Enum <= 23) then
							if (Enum > 22) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								local T;
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							end
						elseif (Enum <= 24) then
							Stk[Inst[2]][Inst[3]] = Inst[4];
						elseif (Enum > 25) then
							Stk[Inst[2]] = {};
						else
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						end
					elseif (Enum <= 29) then
						if (Enum <= 27) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						elseif (Enum > 28) then
							do
								return;
							end
						else
							local B;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 30) then
						local B;
						local A;
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
					elseif (Enum > 31) then
						VIP = Inst[3];
					else
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				elseif (Enum <= 37) then
					if (Enum <= 34) then
						if (Enum > 33) then
							Upvalues[Inst[3]] = Stk[Inst[2]];
						else
							local Edx;
							local Results, Limit;
							local B;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 35) then
						local A = Inst[2];
						Stk[A] = Stk[A]();
					elseif (Enum == 36) then
						if (Stk[Inst[2]] <= Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						for Idx = Inst[2], Inst[3] do
							Stk[Idx] = nil;
						end
					end
				elseif (Enum <= 40) then
					if (Enum <= 38) then
						if (Stk[Inst[2]] == Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 39) then
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local B;
						local A;
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
					end
				elseif (Enum <= 41) then
					Stk[Inst[2]] = Inst[3] ~= 0;
				elseif (Enum > 42) then
					Stk[Inst[2]] = Stk[Inst[3]];
				else
					local A = Inst[2];
					Stk[A] = Stk[A](Stk[A + 1]);
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!403Q00030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q7470476574031C3Q00682Q7470733A2Q2F7369726975732E6D656E752F7261796669656C64030A3Q0047657453657276696365030A3Q0052756E5365727669636503073Q00506C6179657273030C3Q0043726561746557696E646F7703043Q004E616D65030B3Q00446F6C61726F7620487562030C3Q004C6F6164696E675469746C65030F3Q004C6F6164696E675375627469746C65030A3Q00627920646F6C61726F7603053Q005468656D6503083Q004461726B426C7565030D3Q00546F2Q676C654B657962696E6403043Q00456E756D03073Q004B6579436F646503013Q004B03133Q00436F6E66696775726174696F6E536176696E6703073Q00456E61626C65642Q01030A3Q00466F6C6465724E616D65030A3Q00446F6C61726F7648756203083Q0046696C654E616D65030A3Q004D61696E436F6E66696703073Q00446973636F7264010003063Q00496E76697465034Q00030D3Q0052656D656D6265724A6F696E7303093Q004B657953797374656D03093Q0043726561746554616203043Q004D61696E03043Q00686F6D6503063Q00506C6179657203043Q0075736572026Q00F03F030D3Q0043726561746553656374696F6E030C3Q00437265617465546F2Q676C6503153Q00456E61626C652053702Q65642028434672616D6529030C3Q0043752Q72656E7456616C756503043Q00466C616703103Q00546F2Q676C654C6F63616C53702Q656403083Q0043612Q6C6261636B030C3Q00437265617465536C6964657203103Q0053702Q6564204D756C7469706C69657203053Q0052616E6765026Q003E4003093Q00496E6372656D656E74026Q002440030F3Q00536C6964657253702Q65644D756C74026Q003440030A3Q004A756D7020506F776572030A3Q00546F2Q676C654A756D7003133Q004A756D7020506F776572202F20486569676874026Q003940025Q00407F40026Q00144003063Q0053752Q666978030E3Q004A756D70506F77657256616C7565030B3Q004C6F63616C506C61796572030E3Q00436861726163746572412Q64656403073Q00436F2Q6E65637400823Q0012213Q00013Q00122Q000100023Q00202Q00010001000300122Q000300046Q000100039Q0000026Q0001000200122Q000100023Q00202Q00010001000500122Q000300064Q001F000100030002001214000200023Q00202Q00020002000500122Q000400076Q00020004000200202Q00033Q00084Q00053Q000800302Q00050009000A00302Q0005000B000A00302Q0005000C000D00302Q0005000E000F001204000600113Q00200B00060006001200202Q00060006001300102Q0005001000064Q00063Q000300302Q00060015001600302Q00060017001800302Q00060019001A00102Q0005001400064Q00063Q000300302Q00060015001C0030180006001D001E0030270006001F001600102Q0005001B000600302Q00050020001C4Q00030005000200202Q00040003002100122Q000600223Q00122Q000700236Q00040007000200202Q00050003002100122Q000700243Q001206000800254Q001F0005000800022Q0025000600063Q001206000700264Q002900085Q00061300093Q000100052Q002B3Q00064Q002B3Q00074Q002B3Q00084Q002B3Q00024Q002B3Q00013Q002011000A0005002700122Q000C00246Q000A000C000200202Q000B000500284Q000D3Q000400302Q000D0009002900302Q000D002A001C00302Q000D002B002C000613000E0001000100042Q002B3Q00084Q002B3Q00094Q002B3Q00074Q002B3Q00063Q001012000D002D000E4Q000B000D000100202Q000B0005002E4Q000D3Q000600302Q000D0009002F4Q000E00023Q00122Q000F00263Q00122Q001000316Q000E0002000100100E000D0030000E003018000D00320026003018000D002A0033003018000D002B0034000613000E0002000100032Q002B3Q00074Q002B3Q00084Q002B3Q00093Q001007000D002D000E4Q000B000D00014Q000B5Q00122Q000C00353Q00202Q000D000500284Q000F3Q000400302Q000F0009003600302Q000F002A001C00302Q000F002B003700061300100003000100012Q002B3Q000B3Q001016000F002D00104Q000D000F000200202Q000E0005002E4Q00103Q000700302Q0010000900384Q001100023Q00122Q001200393Q00122Q0013003A6Q00110002000100100E00100030001100301800100032003B0030180010003C001E0030180010002A00350030180010002B003D00061300110004000100022Q002B3Q000C4Q002B3Q000B3Q00100E0010002D00112Q001F000E00100002000613000F0005000100022Q002B3Q000B4Q002B3Q000C3Q000605000B007900013Q0004203Q007900012Q002B0010000F4Q0002001000010001001204001000023Q00200F00100010000700200F00100010003E00200F00100010003F00201900100010004000061300120006000100012Q002B3Q000F4Q000C0010001200012Q001D3Q00013Q00073Q000B3Q00030A3Q00446973636F2Q6E656374028Q00030B3Q004C6F63616C506C6179657203093Q00436861726163746572030E3Q00436861726163746572412Q64656403043Q0057616974030C3Q0057616974466F724368696C6403083Q0048756D616E6F6964026Q00144003093Q0048656172746265617403073Q00436F2Q6E656374012A4Q001000015Q0006050001000800013Q0004203Q000800012Q001000015Q0020190001000100012Q000A0001000200012Q0025000100014Q002200016Q00223Q00014Q0010000100023Q0006050001000E00013Q0004203Q000E00010026243Q000F000100020004203Q000F00012Q001D3Q00014Q0010000100033Q00200F00010001000300200F00020001000400062800020017000100010004203Q0017000100200F0002000100050020190002000200062Q002A000200020002002019000300020007001206000500083Q001206000600094Q001F0003000600020006280003001E000100010004203Q001E00012Q001D3Q00014Q0010000400043Q00200F00040004000A00201900040004000B00061300063Q000100052Q002B3Q00014Q002B3Q00024Q002B3Q00034Q00108Q002B8Q001F0004000600022Q002200046Q001D3Q00013Q00013Q00083Q0003093Q0043686172616374657203063Q00506172656E74030A3Q00446973636F2Q6E656374030D3Q004D6F7665446972656374696F6E03093Q004D61676E6974756465028Q00030B3Q005472616E736C6174654279026Q00244001244Q001000015Q00200F0001000100012Q0010000200013Q0006260001000C000100020004203Q000C00012Q0010000100023Q0006050001000C00013Q0004203Q000C00012Q0010000100023Q00200F00010001000200062800010015000100010004203Q001500012Q0010000100033Q0006050001001200013Q0004203Q001200012Q0010000100033Q0020190001000100032Q000A0001000200012Q0025000100014Q0022000100034Q001D3Q00014Q0010000100023Q00200F00010001000400200F000100010005000E0100060023000100010004203Q002300012Q0010000100023Q00201E0001000100044Q000200013Q00202Q0002000200074Q000400046Q00040001000400202Q0004000400084Q000400046Q0002000400012Q001D3Q00017Q00013Q00030A3Q00446973636F2Q6E65637401104Q00227Q0006053Q000700013Q0004203Q000700012Q0010000100014Q0010000200024Q000A0001000200010004203Q000F00012Q0010000100033Q0006050001000F00013Q0004203Q000F00012Q0010000100033Q0020190001000100012Q000A0001000200012Q0025000100014Q0022000100034Q001D3Q00019Q002Q0001084Q00228Q0010000100013Q0006050001000700013Q0004203Q000700012Q0010000100024Q002B00026Q000A0001000200012Q001D3Q00017Q000B3Q0003043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C6179657203093Q0043686172616374657203163Q0046696E6446697273744368696C64576869636849734103083Q0048756D616E6F6964030C3Q005573654A756D70506F77657203093Q004A756D70506F776572026Q004940030A3Q004A756D7048656967687402CD5QCC1C40011A4Q00227Q0006283Q0019000100010004203Q00190001001204000100013Q00200F00010001000200200F00010001000300200F0001000100040006050001001000013Q0004203Q00100001001204000100013Q00201C00010001000200202Q00010001000300202Q00010001000400202Q00010001000500122Q000300066Q0001000300020006050001001800013Q0004203Q0018000100200F0002000100070006050002001700013Q0004203Q001700010030180001000800090004203Q001800010030180001000A000B2Q001D3Q00014Q001D3Q00017Q00093Q0003043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C6179657203093Q0043686172616374657203163Q0046696E6446697273744368696C64576869636849734103083Q0048756D616E6F6964030C3Q005573654A756D70506F77657203093Q004A756D70506F776572030A3Q004A756D70486569676874011A4Q00228Q0010000100013Q0006050001001900013Q0004203Q00190001001204000100013Q00200F00010001000200200F00010001000300200F0001000100040006050001001100013Q0004203Q00110001001204000100013Q00201C00010001000200202Q00010001000300202Q00010001000400202Q00010001000500122Q000300066Q0001000300020006050001001900013Q0004203Q0019000100200F0002000100070006050002001800013Q0004203Q0018000100100E000100083Q0004203Q0019000100100E000100094Q001D3Q00017Q00093Q0003043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C6179657203093Q0043686172616374657203163Q0046696E6446697273744368696C64576869636849734103083Q0048756D616E6F6964030C3Q005573654A756D70506F77657203093Q004A756D70506F776572030A3Q004A756D70486569676874001A4Q00107Q0006283Q0004000100010004203Q000400012Q001D3Q00013Q0012043Q00013Q00200F5Q000200200F5Q000300200F00013Q00040006280001000B000100010004203Q000B00012Q001D3Q00013Q002019000200010005001206000400064Q001F00020004000200062800020011000100010004203Q001100012Q001D3Q00013Q00200F0003000200070006050003001700013Q0004203Q001700012Q0010000300013Q00100E0002000800030004203Q001900012Q0010000300013Q00100E0002000900032Q001D3Q00017Q00033Q0003043Q007461736B03043Q0077616974029A5Q99D93F00073Q00120D3Q00013Q00206Q000200122Q000100038Q000200019Q006Q000100016Q00017Q00", GetFEnv(), ...);

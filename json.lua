--****************************************************************************--
--******************************* Lunar-JSON *********************************--
--****************************************************************************--
--[[
  Extremely fast pure Lua json encoding & decoding module
  Version 0.1
  Licenced under MIT
  Copyright (c) 2021 CptMercury

  Information about the JSON format:
  https://www.json.org/json-en.html
  https://tools.ietf.org/html/rfc8259
--]]
--****************************************************************************--
local checkarg, error, tonumber = checkArg, error, tonumber
local mtype, next, type = math.type, next, type
local find, format, gsub = string.find, string.format, string.gsub
local match, sub = string.match, string.sub
local concat, move, sort = table.concat, table.move, table.sort
local char, codepoint = utf8.char, utf8.codepoint
--****************************************************************************--
local json = {}

-- constants
local INF = math.huge
local NAN = 0/0
--****************************************************************************--
--******************************** Decoding **********************************--
--****************************************************************************--
local escapes = {
  ["\""] = "\"",
  ["\\"] = "\\",
  ["b"] = "\b",
  ["f"] = "\f",
  ["n"] = "\n",
  ["r"] = "\r",
  ["t"] = "\t",
  ["/"] = "/"
}

local numbers = {
  '^[%+%-]?%d+%.?*%d*()',
  '^[%+%-]?%d+%.?*%d*[eE][%+%-]?%d+()',
  '^[%+%-]?%.?*%d+()',
  '^[%+%-]?%.?*%d+[eE][%+%-]?%d+()',
  -- only use last one if not strict
  '^[%+%-]?0[xX][%da-fA-F]+()'
}

local function count(s, pat)
  local _, c = s:gsub(pat, "")
  return c
end

--[[
 * generate error message of form:
 * "Line: x:y (char: z): some more information"
 * where x is the line, y is the column and z is the character/byte
]]
local function decode_error(msg, s, pos)
  s = s:sub(1, pos)
  local line = count(s, '\n') + 1
  local col = s:reverse():find('\n', 1) - 1
  local errmsg = ("Line %d column %d (char %d): %s"):format(line, col, pos, msg)
  error(errmsg, 2)
end

-- unique object to indicate failure to produce value
local NOVALUE = {}
local parse_array, parse_object, parse_string

--[[
 * searches for next non-white space token and extracts value
 * @param s: source string
 * @param pos: current position in string
 * @param strict: boolean; whether or not parse in a strict (rfc8259)
 *                conform manner
]]
local function scan(s, pos, strict)
  local p1, p2, tok = find(s, '(%S)', pos)
  if tok == "\"" then
    return parse_string(s, p2+1, strict)
  elseif tok == "[" then
    return parse_array(s, p2+1, strict)
  elseif tok == "{" then
    return parse_object(s, p2+1, strict)
  elseif tok == "t" and find(s, '^true', p2) then
    return true, p2 + 4
  elseif tok == "f" and find(s, '^false', p2) then
    return false, p2 + 5
  elseif tok == "n" and find(s, '^null', p2) then
    return json.null, p2 + 4
  elseif not strict and tok == "I" and find(s, '^Infinity', p2) then
    return INF, p2 + 8
  elseif not strict and tok == "-" and find(s, '^%-Infinity', p2) then
    return -INF, p2 + 9
  elseif not strict and tok == "N" and find(s, '^NAN', p2) then
    return NAN, p2 + 3
  else  -- should be a number
    for i = 1, strict and 4 or 5 do
      local n1, n2 = find(s, numbers[i], p2)
      if n1 then
        return tonumber(sub(s, n1, n2)), n2 + 1
      end
    end
  end
  -- no valid json value could be identified
  return NOVALUE, p1
end

function parse_string(s, pos, strict)
  local p1, p2 = find(s, '^[^\\\0-\x1f]-"', pos)
  -- no escape sequence found, return string without processing
  if p1 then
    return sub(s, p1, p2-1), p2+1
  end
  local str = ""
  local start = pos - 1
  while true do
    local chunk, p, tok = match(s, '(.-)()(["\\\0-\x1f])', pos)
    if not chunk then
      decode_error("Unfinished string starting at", s, start)
    end
    if tok == "\"" then -- end of string
      return str..chunk, p + 1
    elseif tok == "\\" then
      local esc = sub(s, p+1, p+1)
      if esc == "u" then
        -- REVIEW: use tonumber and then char while checking results
        --         in between those calls
        local c = pcall(char, "0x"..sub(s, p+1, p+4))
        if not c then
          decode_error("Invalid \\uXXXX sequence", s, p)
        end
        str = str..(chunk..c)
        pos = p + 6 -- REVIEW: +6 correct?
      elseif escapes[esc] then
        str = str..(chunk..escapes[esc])
        pos = p + 2 -- REVIEW: +2 correct?
      else
        -- TODO: use format to add what invalid escape sequence was found
        decode_error("Invalid \\escape sequence", s, pos)
      end
    else
      if strict then
        -- TODO: use format to add what invalid control character was found
        decode_error("Invalid control character", s, pos)
      else
        str = str..(chunk..terminator)
        pos = p + 2
      end
    end
  end
end

function parse_array(s, pos, strict)
  local res, i = {}, 1
  local p1, p2, tok = find(s, '(%S)', pos)
  if tok == "]" then  -- empty array
    return res, p2 + 1
  end
  while true do
    local val, p = scan(s, p2, strict)
    if val ~= NOVALUE then
      res[i] = val
      i = i + 1
    else
      decode_error("Value expected", s, p)
    end
    p1, p2, tok = find(s, '(%S)', p)
    if tok == "]" then
      return res, p2 + 1
    elseif tok ~= "," then
      decode_error("Seperator ',' expected", s, p2)
    end
    p2 = p2 + 1
  end
end

function parse_object(s, pos, strict)
  local res = {}
  local p1, p2, tok = find(s, '(%S)', pos)
  if tok == "}" then  -- empty object
    return res, p2 + 1
  end
  while true do
    p1, p2, tok = find(s, '(%S)', p2)
    if tok ~= "\"" then
      decode_error("Property name enclosed in double quotes expected", s, p2)
    end
    local key, p = parse_string(s, p2+1, strict)
    p1, p2, tok = find(s, '(%S)', p)
    if tok ~= ":" then
      decode_error("Seperator ':' expected", s, p2)
    end
    local val, p = scan(s, p2+1, strict)
    if val ~= NOVALUE then
      res[key] = val
    else
      decode_error("Value expected", s, p)
    end
    p1, p2, tok = find(s, '(%S)', p)
    if tok == "}" then
      return res, p2 + 1
    elseif tok ~= "," then
      decode_error("Seperator ',' expected", s, p2)
    end
    p2 = p2 + 1
  end
end

function json.decode(s, strict)
  checkarg(1, s, "string")
  checkarg(2, strict, "nil", "boolean")
  return pcall(scan, s, 1, strict)
end
--****************************************************************************--
--******************************** Encoding **********************************--
--****************************************************************************--
local function encode_error(msg)
  return error(msg, 2)
end

local serialize

local function serialize_number(n, allow_const)
  local res
  if n == INF then
    res = "Infinity"
  elseif n == -INF then
    res = "-Infinity"
  elseif n ~= n then
    res = "NAN"
  else
    return format(mtype(n) == "integer" and '%d' or '%f', n)
  end

  if not allow_const then
    encode_error("Number cannot be a constant (NaN, math.huge, -math.huge)")
  else
    return res
  end
end

local function serialize_string(s, ascii_only, esc_slash)
  if ascii_only then
    -- substitute all non-ascii characters for corresponding \uXXXX sequence
    s = gsub(s, '[\xC2-\xF4][\x80-\xBF]*', function(a)
      return format('\\u%04X', codepoint(a))
    end)
  end
  if esc_slash then
    -- escape all slashes
    s = gsub(s, '/', '\\/')
  end
  return format('%q', s)
end

local function serialize_array(t, prev_indent, indent, args, saved)
  local val_sep = args.val_sep
  local curr_indent = prev_indent..indent
  local res, i = {}, 1
  local v = t[i]

  while v ~= nil do
    res[i] = curr_indent..serialize(v, curr_indent, indent, args, saved)..val_sep
    i = i + 1
    v = t[i]
  end
  -- use last valid index to check for other existing keys
  -- if there are, it is not a pure array
  if next(t, i-1) then
    encode_error("Table is not an array.")
  end
  res[0], res[i-1], res[i] = "[", res[i-1]:sub(1, -#val_sep-1), prev_indent.."]"

  return concat(res, args.line_sep, 0)
end

local function serialize_object(t, prev_indent, indent, args, saved)
  local ascii_only, esc_slash = args.ascii_only, args.esc_slash
  local name_val_sep, val_sep = args.name_val_sep, args.val_sep
  local check_keys = args.check_keys
  local curr_indent = prev_indent..indent
  local res, i = {}, 1

  for k, v in pairs(t) do
    if type(k) == "string" then
      res[i] = format('%s%s%s%s%s', curr_indent, serialize_string(k, ascii_only,
        esc_slash), name_val_sep, serialize(v, curr_indent, indent, args, saved),
        val_sep)
      i = i + 1
      -- REVIEW: what does check_keys do?
    elseif check_keys then
      encode_error("Invalid key type. String expected, got "..type(k))
    end
  end
  if args.sort_keys then
    sort(res)
  end
  res[0], res[i-1], res[i] = "{", res[i-1]:sub(1, -#val_sep-1), prev_indent.."}"

  return concat(res, args.line_sep, 0)
end

function serialize(obj, prev_indent, indent, args, saved)
  local t = type(obj)
  if obj == json.null then
    return "null"

  elseif t == "boolean" then
    return format('%q', obj)

  elseif t == "number" then
    return serialize_number(obj, args.allow_const)

  elseif t == "string" then
    return serialize_string(obj, args.plain_ascii, args.esc_slash)

  elseif t == "table" then
    if saved[obj] then
      encode_error("Cannot serialize tables with recursive entries.")
    else
      saved[obj] = true
    end

    local first_key = type(next(obj))
    if first_key == "nil" then
      -- empty table; is interpreted as empty array
      return prev_indent..indent.."[]"
    elseif first_key == "number" then
      -- table is a array
      return serialize_array(obj, prev_indent, indent, args, saved)
    else
      -- table is an object
      return serialize_object(obj, prev_indent, indent, args, saved)
    end

  else
    encode_error("Cannot serialize value of type '"..type(obj).."'")
  end
end

function json.encode(obj, ascii_only, esc_slash, check_keys, sort_keys,
  allow_const, indent, seperators)
  checkarg(1, obj, "table", "string", "number", "boolean")
  checkarg(2, ascii_only, "boolean", "nil")
  checkarg(3, esc_slash, "boolean", "nil")
  checkarg(4, check_keys, "boolean", "nil")
  checkarg(5, sort_keys, "boolean", "nil")
  checkarg(6, allow_const, "boolean", "nil")
  checkarg(7, indent, "string", "number", "nil")
  checkarg(8, seperators, "table", "nil")

  local line_sep, name_val_sep, val_sep

  ascii_only  = ascii_only  == nil and true or ascii_only
  esc_slash   = esc_slash   == nil and true or esc_slash
  check_keys  = check_keys  == nil and true or check_keys
  sort_keys   = sort_keys   == nil and false or sort_keys
  allow_const = allow_const == nil and false or allow_const

  if seperators then
    name_val_sep, val_sep = seperators[1], seperators[2]
  else
    name_val_sep, val_sep = ": ", not indent and ", " or ","
  end

  if indent then
    indent = type(indent) == "number" and rep(' ', indent) or indent
    line_sep = "\n"
  else
    indent = ""
    line_sep = ""
  end

  local args = {
    ascii_only = ascii_only,
    esc_slash = esc_slash,
    check_keys = check_keys,
    sort_keys = sort_keys,
    allow_const = allow_const,
    line_sep = line_sep,
    name_val_sep = name_val_sep,
    val_sep = val_sep
  }

  return pcall(serialize, obj, "", indent, args, {})
end
--****************************************************************************--
return json

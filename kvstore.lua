--[[--

key-value store on sqlite for lua
keys and values are arbitrary byte strings
dependencies: lsqlite3

db = kvstore.open(filename)
db = kvstore.open_memory()

for name,map in db.next,db do
	...
end

map = db:getmap(name)

v=map:get(k)

map:set(k,v)

for k,v in map.next, map do
	...
end

db:trans(function() -- write transaction
	...
end)

db:trans(function() -- read-only transaction
	...
end,true)

size=db:size() -- total db size in kb

Copyright (C)2022 Kimapr

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject
to the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY
KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE
WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
--]]--

local sql=require"lsqlite3"
local u={}
function u.str2hex(bstr)
	return string.gsub(bstr,".",function(a)
		return string.format("%.2x",string.byte(a));
	end)
end

function u.hex2str(hstr)
	assert(#hstr%2==0,"invalid hex string")
	return string.gsub(hstr,"..",function(a)
		return string.char((assert(tonumber(a,16),"invalid hex string")))
	end)
end
local m={}
local db={}
local map={}
db.__index=db
map.__index=map

local function ts(t)
	local s=table.concat(t,";\n")..";"
	return s
end

local function new(d,er)
	if not d then return d,er end
	local obj=setmetatable({__db=d},db)
	d:busy_timeout(30*1000*60*60*24) -- 1 month
	d:exec [=[
		PRAGMA journal_mode = WAL;
		PRAGMA synchronous = NORMAL;
		PRAGMA wal_autocheckpoint = 1000;
		PRAGMA wal_checkpoint(TRUNCATE);
	]=]
	d:rollback_hook(obj.__trans_abort,obj)
	obj.__maps=setmetatable({},{__mode="v"})
	obj.__stmts=setmetatable({},{__mode="v"})
	return obj
end

local stmtmt={}
-- probably not needed and doesnt works in 5.1 anyway
--[[function stmtmt:__gc()
	db.__stmts[self.tx]=nil
	self.s:finalize()
end]]

local errmt={}
local codes={}
for k,v in ipairs{
	"OK","ERROR","INTERNAL","PERM","ABORT","BUSY",
	"LOCKED","NOMEM","READONLY","INTERRUPT","IOERR",
	"CORRUPT","NOTFOUND","FULL","CANTOPEN","PROTOCOL",
	"EMPTY","SCHEMA","TOOBIG","CONSTRAINT","MISMATCH",
	"MISUSE","NOLFS","FORMAT","RANGE","NOTADB","ROW","DONE"
} do
	codes[sql[v]]=v
end
function errmt:__tostring()
	return ("db error (%s): %s"):format(self.code,self.msg)
end
local function errobj(code,msg)
	return setmetatable({code=codes[code],msg=msg},errmt)
end

local function wstmt(db,stmt,tx)
	return setmetatable({s=stmt,db=db,tx=tx},stmtmt)
end

function m.is_dberr(err)
	return getmetatable(err)==errmt
end

function db:__exec(tx)
	local errc=self.__db:exec(tx)
	assert(errc==sql.OK,errobj(errc,self.__db:errmsg()))
end

local function assprep(db,tx)
	local ok,err=db:prepare(tx)
	if not ok then error(errobj(err,errobj(db:errmsg()))) end
	return ok
end

function db:__rexeca(tx,...)
	local db=self.__db
	local ok,err
	local stmt=self.__stmts[tx] or wstmt(db,assprep(db,tx),tx)
	self.__stmts[tx]=stmt
	stmt=stmt.s
	return self:__rexecs(stmt,...)
end

function db:__rexecn(tx,...)
	local db=self.__db
	local stmt=assprep(db,tx)
	return self:__rexecs(stmt,...)
end

function db:__rexecs(stmt,...)
	local db=self.__db
	local errc=stmt:bind_values(...)
	assert(errc==sql.OK,errobj(errc,db:errmsg()))
	local r={}
	for n=1,math.huge do
		local errc=stmt:step()
		if errc==sql.ROW then
			r[#r+1]=stmt:get_named_values()
		elseif errc==sql.DONE then
			break
		elseif errc==sql.ERROR then
			error(errobj(stmt:reset(),db:errmsg()))
		else
			stmt:reset()
			error(errobj(errc,db:errmsg()))
		end
	end
	stmt:reset()
	r.changes=db:changes()
	return r
end

local function tohname(name)
	return "MTBL"..u.str2hex(name)
end

local function fromhname(name)
	return u.hex2str(name:sub(5,-1))
end

function m.open(fname)
	return new(sql.open(fname))
end

function m.open_memory()
	return new(sql.open_memory())
end

function db:size()
	assert(not self.__tx_aborted,"aborted transaction")
	local t={}
	local ps=self:__rexecn("PRAGMA page_size")[1].page_size
	local total=self:__rexecn("PRAGMA page_count")[1].page_count
	local free=self:__rexecn("PRAGMA freelist_count")[1].freelist_count
	return {physical=total*ps,content=total*ps-free*ps}
end

function db:maxsize(n)
	assert(not self.__tx_aborted,"aborted transaction")
	local ps=self:__rexecn("PRAGMA page_size")[1].page_size
	if not n then
		return self:__rexecn("PRAGMA max_page_count")[1].max_page_count*ps
	end
	return self:__rexecn(("PRAGMA max_page_count=%s"):format(math.ceil(n/ps)))[1].max_page_count*ps
end

function db:close()
	local db=self.__db
	db:close_vm()
	assert(db:close()==sql.OK)
end

local function numstr(e)
	if type(e)=="number" then return ""..e end
	return e
end

function db:exists(name)
	name=numstr(name)
	assert(not self.__tx_aborted,"aborted transaction")
	assert(type(name)=="string","non-string name")
	local hname=tohname(name)
	local i=
		("SELECT name FROM sqlite_master WHERE type='table' AND name='%s'")
		:format(hname)
	local res=self:__rexeca(i)
	return not not res[1]
end

function db:getmap(name)
	name=numstr(name)
	assert(type(name)=="string","non-string name")
	assert(not self.__tx_aborted,"aborted transaction")
	assert((not self.__tx or self.__tx_write) or db:exists(name),"read-only transaction")
	local hname=tohname(name)
	local i=
		("CREATE TABLE IF NOT EXISTS %s(Key PRIMARY KEY NOT NULL COLLATE BINARY,Value) WITHOUT ROWID")
		:format(hname)
	self:__exec(i)
	local obj=self.__maps[name] or setmetatable({
		__db=self,
		__name=name,
		__hname=hname
	},map)
	self.__maps[name]=obj
	return obj
end

function db:next(name)
	assert(type(name)=="string" or name==nil,"non-string name")
	assert(not self.__tx_aborted,"aborted transaction")
	local k=name and tohname(name) or ""
	local i=("SELECT name FROM sqlite_master WHERE type='table' AND name > ? ORDER BY name LIMIT 1")
	local res=self:__rexeca(i,k)
	while true do
		local ret=self:__rexeca(i,k)
		if not ret[1] then break end
		if ret[1] and ret[1].name:sub(1,4)=="MTBL" then
			local name=fromhname(ret[1].name)
			return name,self:getmap(name)
		elseif ret[1] then
			k=ret[1].Key
		end
	end
	return nil
end

function db:__trans_nested(fn,r)
	assert(self.__tx_write or r,"read-only transaction")
	self.__tx=self.__tx+1
	local t=self.__tx
	self:__exec(("SAVEPOINT _%s")
		:format(self.__tx))
	local ok,err=xpcall(fn,debug.traceback)
	self.__tx=self.__tx-1
	if self.__tx_aborted then
		if not ok then error(err,0) end
		error("unexpected rollback")
	end
	local roll
	if not ok or not err then
		pcall(self.__exec,self,("ROLLBACK TRANSACTION TO _%s")
			:format(t))
		roll=true
	end
	pcall(self.__exec,self,("RELEASE SAVEPOINT _%s")
		:format(t))
	if not ok then
		error(err,0)
	end
	return not roll
end

function db:__trans_abort()
	assert(self.__tx,"rollback outside of tx")
	self.__tx_aborted=true
end

function db:trans(fn,r)
	assert(not self.__tx_aborted,"aborted transaction")
	if self.__tx then
		return self:__trans_nested(fn,r)
	end
	self.__tx_write=not r
	self.__tx=0
	self:__exec(("BEGIN %s TRANSACTION")
		:format((not r) and "IMMEDIATE" or "DEFERRED"))
	local ok,err=xpcall(fn,debug.traceback)
	local abrt=self.__tx_aborted
	self.__tx,self.__tx_write,self.__tx_aborted=nil
	if abrt then
		if not ok then error(err,0) end
		error("unexpected rollback")
	end
	if not ok or not err then
		self:__exec("ROLLBACK TRANSACTION")
		if not ok then
			error(err,0)
		end
		return false
	end
	self:__exec("COMMIT TRANSACTION")
	return true
end

function map:drop()
	local hname=self.__hname
	local tbl,self=self,self.__db
	assert(not self.__tx_aborted,"aborted transaction")
	assert(not self.__tx or self.__tx_write,"read-only transaction")
	local i=
		("DROP TABLE %s")
		:format(hname)
	self:__exec(i)
end

function map:set(k,v)
	k,v=numstr(k),numstr(v)
	assert(type(k)=="string","non-string key")
	assert(type(v)=="string" or v==nil,"non-string value")
	local hname=self.__hname
	local tbl,self=self,self.__db
	assert(not self.__tx_aborted,"aborted transaction")
	assert(not self.__tx or self.__tx_write,"read-only transaction")
	k="_"..k
	if not v then
		local i=
			("DELETE FROM %s WHERE Key = ?")
			:format(hname)
		self:__rexeca(i,k)
		return
	end
	local i=
		("INSERT INTO %s (Key,Value) VALUES (?1,?2) ON CONFLICT(Key) DO UPDATE SET Value=excluded.Value")
		:format(hname)
	self:__rexeca(i,k,v)
end

function map:get(k)
	k=numstr(k)
	assert(type(k)=="string","non-string key")
	local hname=self.__hname
	local tbl,self=self,self.__db
	assert(not self.__tx_aborted,"aborted transaction")
	k="_"..k
	local i=
		("SELECT * FROM %s WHERE Key = ?")
		:format(hname)
	local ret=self:__rexeca(i,k)
	return ret[1] and ret[1].Value or nil
end

function map:next(k)
	assert(type(k)=="string" or k==nil,"non-string key")
	local hname=self.__hname
	local tbl,self=self,self.__db
	assert(not self.__tx_aborted,"aborted transaction")
	k=k and "_"..k or ""
	local i=
		("SELECT * FROM %s WHERE Key > ? ORDER BY Key LIMIT 1")
		:format(hname)
	while true do
		local ret=self:__rexeca(i,k)
		if not ret[1] then break end
		if ret[1] and ret[1].Key:sub(1,1)=="_" then
			return ret[1].Key:sub(2,-1),ret[1].Value
		elseif ret[1] then
			k=ret[1].Key
		end
	end
	return nil
end

return m

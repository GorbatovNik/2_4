package.path = ".\\..\\?.lua;" .. package.path
require('class')
require('FiniteAutomaton')
local V = {"h", "q", "doll", "eq", "a", "x", "i", "o", "m", "n", "t", "e", "r", "u", "l", "p", "s", "ln", "ws", "ast", "az", "eof", "oth", "lparen", "rparen", "lparen_curve", "rparen_curve", "altern"}
local Q = {"q0", "NTm", "FNTm", "FNTmh", "Tm", "Tmq", "FTm", "WS", "FWS", "KW", "KW$", "FKW", "Comm", "FComm", }
local d = {
	q0 = {
		lambda = { "NTm", "WS", "Tm", "KW", "Comm"}
	},
	NTm = {
		az = {"FNTm"},
		a = {"FNTm"},
		x = {"FNTm"},
		i = {"FNTm"},
		o = {"FNTm"},
		m = {"FNTm"},
		n = {"FNTm"},
		t = {"FNTm"},
		e = {"FNTm"},
		r = {"FNTm"},
		u = {"FNTm"},
		l = {"FNTm"},
	},
	FNTm = {
		az = {"FNTm"},
		a = {"FNTm"},
		x = {"FNTm"},
		i = {"FNTm"},
		o = {"FNTm"},
		m = {"FNTm"},
		n = {"FNTm"},
		t = {"FNTm"},
		e = {"FNTm"},
		r = {"FNTm"},
		u = {"FNTm"},
		l = {"FNTm"},
		h = {"FNTmh"}
	},
	Tm = {
		q = {"Tmq"}
	},
	Tmq = {
		-- all \ { q, eof } = {"Tmq"}
		q = {"FTm"}
	},
	WS = {
		ws = {"FWS"},
		ln = {"FWS"}
	},
	FWS = {
		ws = {"FWS"},
		ln = {"FWS"}
	},
	KW = {
		eq = {"FKW"},
		doll = {"KW$"},
        eof = {"FKW"},
		lparen = {"FKW"},
		rparen = {"FKW"},
		lparen_curve = {"FKW"},
		rparen_curve = {"FKW"},
		altern = {"FKW"},
		-- ln = {"FKW"}
	},
	Comm = {
		ast = {"FComm"},
	},
	FComm = {
		-- all \ { ln, eof } = {"FComm"}
	}
}
local function addTrans(tokens, start, finish, others)
	local ss = {}
	local tokens_map = list2map(tokens)
	if others then
		for _, v in ipairs(V) do
			if not tokens_map[v] then
				table.insert(ss, v)
			end
		end
	else
		ss = tokens
	end
	for _, c in ipairs(ss) do
		if not d[start][c] then d[start][c] = {} end
		table.insert(d[start][c], finish)
	end
end
local function addBranches(terms, start, finish)
	for _, term in ipairs(terms) do
		local name = start
		for i = 1, #term do
			local c = string.sub(term,i,i)
			if not d[name] then d[name] = {} end
			if not d[name][c] then d[name][c] = {} end
			if i ~= #term then
				table.insert(d[name][c], name .. c)
				table.insert(Q, name .. c)
				d[name .. c] = {}
			else
				table.insert(d[name][c], finish)
			end
			name = name .. c
		end
	end
end
addBranches({"axiom", "nterm", "term", "rule"}, "KW$", "FKW")
addTrans({"q", "eof"}, "Tmq", "Tmq", true)
addTrans({"ln", "eof"}, "FComm", "FComm", true)
local q0 = "q0"
local F = {FKW = 6, FNTmh = 5, FNTm = 4, FTm = 3, FWS = 2, FComm = 1} -- priority and ids

local file = io.open("input2.txt", "r")
local code = file:read("a")
-- print("PROGRAM:\n" .. code)


local fa = FiniteAutomaton(V, Q, q0, F, d)
fa:det()

local function tokenol2factor(c)
	local b = string.byte(c)
	local lb = string.byte(string.lower(c))
	if c == "'" then
		return "h"
	elseif c == "\"" then
		return "q"
	elseif c == "$" then
		return "doll"
	elseif c  == "=" then
		return "eq"
	elseif c == "(" then
		return "lparen"
	elseif c == ")" then
		return "rparen"
	elseif c == "{" then
		return "lparen_curve"
	elseif c == "}" then
		return "rparen_curve"
	elseif c =="|" then
		return "altern"
	elseif c == "*" then
		return "ast"
	elseif c == "\n" then
		return "ln"
	elseif c == " " or c == "	" then
		return "ws"
	elseif c == string.char(27) then -- end of file
		return "eof"
	elseif  b >= string.byte("A") and b <= string.byte("Z") then
		if string.find("AXIOMNTERUL", c) then
			return string.lower(c)
		else
			return "az"
		end
	else
		return "oth"
	end
end
local function priority2tokenType(n)
	local p2t = {"COMMENT", "WS", "TERM", "NTERM", "NTERM", "KW"}
	return p2t[n]
end

require('Lexer')
local lexer = Lexer(fa, tokenol2factor, code, priority2tokenType)

print("TOKENS:")
local tokens = {}
local token = lexer:nextToken()
while token do
	local toprint = token.domain .. " "
	toprint = toprint .. "(".. tostring(token.startLine) .. ", " .. tostring(token.startPos) .. ")-(" .. tostring(token.finishLine) .. ", " .. tostring(token.finishPos) .. ")"
	if token.value then toprint = toprint .. ": ".. token.value end
	print(toprint)
	table.insert(tokens, token)
	token = lexer:nextToken()
end
print("MESSAGES:")
for _, mess in ipairs(lexer.messages) do
	print(mess)
end

function list_iter (t)
	local i = 0
	local n = #t
	return function ()
			 i = i + 1
			 if i <= n then return t[i] end
		   end
end

local tokenIter = list_iter(tokens)
local token = tokenIter()
local terms = {}
local nterms = {}
local tree = {}
local rules = {}

function parseGrammar()
	local node = {name = "Grammar", children = {}}
	while token.domain ~= "END_OF_PROGRAM" do
		table.insert(node.children, parseDeclaration())
	end

	return node
end

-- Declaration = AxiomDecl | NtermsDecl | TermsDecl | RuleDecl.
function parseDeclaration()
	local node = {name = "Declaration", children = {}}
	if token.domain == "$AXIOM" then
		table.insert(node.children, parseAxiomDecl())
	elseif token.domain == "$NTERM" then
		table.insert(node.children, parseNtermsDecl())
	elseif token.domain == "$TERM" then
		table.insert(node.children, parseTermsDecl())
	elseif token.domain == "$RULE" then
		table.insert(node.children, parseRuleDecl())
	else
		error()
	end

	return node
end

function parseAxiomDecl()
	local node = {name = "AxiomDecl", children = {}}
	if token.domain == "$AXIOM" then
		table.insert(node.children, token)
		token = tokenIter()
		if token.domain == "NTERM" then
			table.insert(node.children, token)
			token = tokenIter()
		else
			error()
		end
	else
		error()
	end

	return node
end

function parseNtermsDecl()
	local node = {name = "NtermsDecl", children = {}}
	if token.domain == "$NTERM" then
		table.insert(node.children, token)
		token = tokenIter()
		if token.domain == "NTERM" then
			table.insert(nterms, token.value)
			table.insert(node.children, token)
			token = tokenIter()
			while token.domain == "NTERM" do
				table.insert(nterms, token.value)
				table.insert(node.children, token)
				token = tokenIter()
			end
		else
			error()
		end
	else
		error()
	end

	return node
end

function parseTermsDecl()
	local node = {name = "TermsDecl", children = {}}
	if token.domain == "$TERM" then
		table.insert(node.children, token)
		token = tokenIter()
		if token.domain == "TERM" then
			table.insert(terms, token.value)
			table.insert(node.children, token)
			token = tokenIter()
			while token.domain == "TERM" do
				table.insert(terms, token.value)
				table.insert(node.children, token)
				token = tokenIter()
			end
		else
			error()
		end
	else
		error()
	end

	return node
end

function parseExpr()
	local node = {name = "Expr", children = {}}
	table.insert(node.children, parseAltern())
	while token.domain == "ALTERN" do
		table.insert(node.children, token)
		token = tokenIter()
		table.insert(node.children, parseAltern())
	end
	
	return node
end

function parseAltern()
	local node = {name = "Altern", children = {}}
	table.insert(node.children, parseConcat())
	while token.domain == "NTERM" or token.domain == "TERM" or token.domain == "LPAREN" or token.domain == "LPAREN_CURVE" do
		table.insert(node.children, parseConcat())
	end

	return node
end

function parseConcat()
	local node = {name = "Concat", children = {}}
	if token.domain == "NTERM" or token.domain == "TERM" then
		table.insert(node.children, token)
		token = tokenIter()
	elseif token.domain == "LPAREN" then
		table.insert(node.children, parseGrouping())
	elseif token.domain == "LPAREN_CURVE" then
		table.insert(node.children, parseOption())
	end

	return node
end

function parseGrouping()
	local node = {name = "Grouping", children = {}}
	if token.domain == "LPAREN" then
		table.insert(node.children, token)
		token = tokenIter()
		table.insert(node.children, parseExpr())
		if token.domain == "RPAREN" then
			table.insert(node.children, token)
			token = tokenIter()
		else
			error()
		end
	else
		error()
	end

	return node
end

function parseOption()
	local node = {name = "Option", children = {}}
	if token.domain == "LPAREN_CURVE" then
		table.insert(node.children, token)
		token = tokenIter()
		table.insert(node.children, parseExpr())
		if token.domain == "RPAREN_CURVE" then
			table.insert(node.children, token)
			token = tokenIter()
		else
			error()
		end 
	else
		error()
	end

	return node
end

function parseRuleDecl()
	local node = {name = "RuleDecl", children = {}}
	if token.domain == "$RULE" then
		table.insert(node.children, token)
		token = tokenIter()
		if token.domain == "NTERM" then
			local left = token.value
			table.insert(node.children, token)
			token = tokenIter()
			if token.domain == "ASSIGN" then
				table.insert(node.children, token)
				token = tokenIter()
				local right = parseExpr()
				table.insert(node.children, right)
				rules[left] = right
			else
				error()
			end
		else
			error()
		end
	else
		error()
	end

	return node
end
tree = parseGrammar()
print("end")

local first = {}
for _, nterm in ipairs(nterms) do
	first[nterm] = {}
end


function TableConcat(t1, t2)
	for i = 1, #t2 do
		t1[#t1+1] = t2[i]
	end

	return t1
end

function haveEps(aFirst)
	for _, f in ipairs(aFirst) do
		if f.domain == "$EPS" then return true end
	end
	
	return false
end

function woEps(aFirst)
	local res = {}
	for _, f in ipairs(aFirst) do
		if f.domain ~= "$EPS" then table.insert(res, f) end
	end

	return res
end

-- function Digamma(node)
-- 	if not idx then idx = 1 end
-- 	if #chain < idx then return {} end

-- 	if #chain > idx then
-- 		local u = {chain[idx]}
-- 		local DigU = Digamma(u)
-- 		if not haveEps(DigU) then
-- 			return DigU
-- 		else
-- 			return TableConcat(woEps(DigU), Digamma(chain, idx + 1))
-- 		end
-- 	end

-- 	local node = chain[idx]

-- 	if node.domain == "TERM" or node.domain == "$EPS" then
-- 		return { node }
-- 	end
-- 	if node.domain == "NTERM" then
-- 		return first[x]
-- 	end
-- 	if node.name == "Expr" then
-- 		local unionFirst = {}
-- 		for u in ipairs(node.children) do
-- 			unionFirst = TableConcat(unionFirst, Digamma)
-- 		end
-- 		return unionFirst
-- 	end
-- 	if node.name == ""




-- 	if 
-- 		local firstX = first[x]
-- 		if haveEps(firstX) then
-- 			return TableConcat(woEps(firstX), Digamma(chain, idx + 1))
-- 		else
-- 			return firstX
-- 		end
-- 	end
-- 	error()
-- end

function getFirstExpr(exprTree)
	local firstList = {}
	for _, alternChild in ipairs(exprTree.children) do
		firstList = TableConcat(firstList, getFirstAltern(alternChild))
	end

	return firstList
end

function getFirstAltern(alternTree, idx)
	if not idx then idx = 1 end
	if not alternTree.children then return {} end
	if #alternTree.children < idx then return {} end
	-- assert(#alternTree.children ~= 0) 
	local firstFirstConcat =  getFirstConcat(alternTree.children[idx])
	local otherFirstConcat =  getFirstAltern(alternTree, idx + 1)

	if not otherFirstConcat or #otherFirstConcat == 0 then
		return firstFirstConcat
	end

	if haveEps(firstFirstConcat) then
		return TableConcat(woEps(firstFirstConcat), otherFirstConcat)
	end

	return firstFirstConcat
end

function getFirstConcat(concatTree)
	assert(#concatTree.children ~=0 )
	if concatTree.children[1].name == "Option" then
		local f = getFirstExpr(concatTree.children[1].children[2])
		if not haveEps(f) then
			return TableConcat(f, {{domain = "$EPS", value = "$EPS"}})
		else
			return f
		end
	elseif concatTree.children[1].name == "Grouping" then
		return getFirstExpr(concatTree.children[1].children[2])
	end
	if not concatTree.children[1].domain then return {} end
	if concatTree.children[1].domain == "TERM" then
		return { concatTree.children[1] }
	elseif concatTree.children[1].domain == "NTERM" then
		return first[concatTree.children[1].value]
	elseif concatTree.children[1].domain == "LPAREN" or concatTree.children[1].domain == "LPAREN_CURVE" then -- no need?
		return getFirstExpr(concatTree.children[2]) 
	end
end


local woRepT2 = {}
local function isDiff(t1, t2)
	if type(t1) ~= "table" then return false end
	local valmap1 = {}
	for _, dom in ipairs(t1) do
		valmap1[dom.value] = true
	end
	local valmap2 = {}
	woRepT2 = {}
	for _, dom in ipairs(t2) do
		if not valmap2[dom.value] then
			valmap2[dom.value] = true
			table.insert(woRepT2, dom)
		end
	end

	local function isIncl(map1, map2)
		for name, _ in pairs(map1) do
			if not map2[name] then return false end
		end

		return true
	end

	return not (isIncl(valmap1, valmap2) and isIncl(valmap2, valmap1))
end

local changed = true
while changed do
	changed = false
	for left, right in pairs(rules) do
		local firstExpr = getFirstExpr(right)

		if isDiff(first[left], firstExpr) then
			changed = true
			first[left] = woRepT2
		end
	end
end

-- function union(set1, set2)
-- 	local set = {}
-- 	for key, value in pairs(set1) do
-- 		set[key] = value
-- 	end
-- 	for key, value in pairs(set2) do
-- 		set[key] = value
-- 	end

-- 	return set
-- end

-- local expandedFirst = {}
-- function expandFirst(symb)
-- 	if expandedFirst[symb] then
-- 		return
-- 	end

-- 	expandedFirst[symb] = {}
-- 	local productions = first[symb]
-- 	for _, prod in ipairs(productions) do
-- 		if prod.domain == "TERM" or prod.domain == "$EPS" then
-- 			expandedFirst[symb][prod.value] = true
-- 		elseif prod.domain == "NTERM" then
-- 			expandFirst(prod.value)
-- 			expandedFirst[symb] = union(expandedFirst[symb], expandedFirst[prod.value])
-- 		end
-- 	end
-- end

for _, nterm in ipairs(nterms) do
	-- expandFirst(nterm)
	local str = ""
	for _, dom in ipairs(first[nterm]) do
		str = str .. "\"" .. dom.value .. "\", "
	end
	print(string.format("FIRST(%s) = {%s}", nterm, str))
end





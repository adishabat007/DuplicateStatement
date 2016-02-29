datatype Statement = Assignment(LHS : seq<Variable>, RHS : seq<Expression>) | Skip | SeqComp(S1 : Statement, S2 : Statement) | 
		IF(B0 : BooleanExpression, Sthen : Statement, Selse : Statement) | DO(B : BooleanExpression, S : Statement) |
		LocalDeclaration(L : seq<Variable>, S0 : Statement);
type Variable = string;
type Expression = string;
type BooleanExpression = string;

method Main()
{
	var S : Statement;
	//S := FromString("i,sum,prod := i+1,sum+i,prod*i;");
	S := Assignment(["i","sum","prod"],["i+1","sum+i","prod*i"]);
	var V := ["sum"];
	//ghost var allVars := glob(S);
	var S' := DuplicateStatement(S,V);
	assert S' == LocalDeclaration(["isum"]+["ii","iprod"]+["fsum"],SeqComp(SeqComp(SeqComp(SeqComp(
		SeqComp(Assignment(["isum"]+["ii","iprod"],V+["i","prod"]),S),Assignment(["fsum"],V)),Assignment(V+["i","prod"],["isum"]+["ii","iprod"])),S),Assignment(V,["fsum"])));
	var result := ToString(S');
	print(result);
	//assert result == "{ var isum,ii,iprod,fsum; isum,ii,iprod := sum,i,prod;i,sum,prod := i+1,sum+i,prod*i;fsum := sum;sum,i,prod := isum,ii,iprod;i,sum,prod := i+1,sum+i,prod*i;sum := fsum; } ";

	//flow-insensitive sliding:
	var SV: Statement, ScoV: Statement;
	S',SV,ScoV := FlowInsensitiveSliding(S,V);
	assert S' == LocalDeclaration(["isum"]+["ii","iprod"]+["fsum"],SeqComp(SeqComp(SeqComp(SeqComp(
		SeqComp(Assignment(["isum"]+["ii","iprod"],V+["i","prod"]),SV),Assignment(["fsum"],V)),Assignment(V+["i","prod"],["isum"]+["ii","iprod"])),ScoV),Assignment(V,["fsum"])));
	assert SV == Assignment(["sum"],["sum+i"]);
	assert ScoV == Assignment(["i","prod"],["i+1","prod*i"]);
	result := ToString(S');
	print(result);

}

// pretty printing...
function method ToString(S : Statement) : string
	//ensures ToString(S) == "i,sum,prod := i+1,sum+i,prod*i;";
{
	match S {
		case Assignment(LHS,RHS) => AssignmentToString(LHS,RHS)
		case Skip => ";"
		case SeqComp(S1,S2) => ToString(S1) + ToString(S2)
		case IF(B0,Sthen,Selse) => "if " + B0 + " {" + ToString(Sthen) + " else " + ToString(Selse) + " } "
		case DO(B,S) => "while (" + B + ") { " + ToString(S) + " } "
		case LocalDeclaration(L,S0) => "{ var " + VariableListToString(L) + "; " + ToString(S0) + " } "
	}
}

function method AssignmentToString(LHS : seq<Variable>, RHS : seq<Expression>) : string
{
	VariableListToString(LHS) + " := " + ExpressionListToString(RHS) + ";"
}

function method VariableListToString(variables : seq<Variable>) : string
{
	if |variables| > 1 then
		variables[0] + "," + VariableListToString(variables[1..])
	else if |variables| > 0 then
		variables[0]
	else
		""
}

function method ExpressionListToString(expressions : seq<Expression>) : string
{
	if |expressions| > 1 then
		expressions[0] + "," + ExpressionListToString(expressions[1..])
	else if |expressions| > 0 then
		expressions[0]
	else
		""
}

// parsing...
function method FromString(str : string) : Statement
	//ensures ToString(FromString(str)) == str;
{
	if str == ";" then
		Skip
	else if |str| > 2 && str[..2] == "if " then
		IF("x == 0",Skip,Skip) // FIXME parse recursively
	else if |str| > 6 && str[..6] == "while " then
		DO("x == 0",Skip) // FIXME parse recursively
	else if |str| > 6 && str[..6] == "{ var " then
		LocalDeclaration([],Skip) // FIXME parse recursively
	else if exists i :: 0 <= i < |str| && str[i] == ';' then
		SeqComp(Skip,Skip) // FIXME parse recursively
	else // assert ValidAssignment(str)
		Assignment(["i","sum","prod"],["i+1","sum+i","prod*i"]) // FIXME parse LHS,RHS
}

predicate method ValidAssignment(str : string)
{
	true // check ":=" with same-length lists to its left and right, the former of distinct variable names and the right of expressions
}

/*
function method freshInit(vars : seq<Variable>, ghost allVars : set<Variable>) : seq<Variable>
	//requires |setOf(vars)| == |vars|;
	requires setOf(vars) < allVars;
	requires forall v :: v in vars ==> "i"+v !in allVars;
	ensures setOf(freshInit(vars,allVars)) !! allVars;
	ensures setOf(freshInit(vars,allVars)) !! allVars;
	ensures |freshInit(vars,allVars)| == |vars|;
{
	if vars == [] then [] else ["i"+vars[0]] + freshInit(vars[1..],allVars+{"i"+vars[0]})
}
*/
function method def(S : Statement) : set<Variable> // FIXME: make it return a set
//	ensures def(S) == {"i","sum","prod"};
{
	match S {
		//case Assignment(LHS,RHS) => set{LHS} // FIXME
		case Skip => {}
		case SeqComp(S1,S2) => def(S1) + def(S2)
		case IF(B0,Sthen,Selse) => def(Sthen) + def(Selse)
		case DO(B,S) => def(S)
		case LocalDeclaration(L,S0) => def(S0) - L
	}
}

function ddef(S : Statement) : set<Variable>
//	ensures ddef(S) == ["i","sum","prod"];
{
	match S {
		//case Assignment(LHS,RHS) => set{LHS} // FIXME
		case Skip => {}
		case SeqComp(S1,S2) => ddef(S1) + ddef(S2)
		case IF(B0,Sthen,Selse) => ddef(Sthen) * ddef(Selse)
		case DO(B,S) => {}
		case LocalDeclaration(L,S0) => ddef(S0) - L
	}
}

function input(S : Statement) : set<Variable>
//	ensures input(S) == ["i","sum","prod"];
{
	match S {
		case Assignment(LHS,RHS) => setOf(LHS) // FIXME (LHS is a sequence of Expression(s), not Variable(s)
		case Skip => {}
		case SeqComp(S1,S2) => input(S1) + (input(S2) - ddef(S1)) // right?
		case IF(B0,Sthen,Selse) => setOf(B0) + input(Sthen) + input(Selse) // FIXME: variables of B0?
		case DO(B,S) => setOf(B0) + input(S) // FIXME: variables of B?
		case LocalDeclaration(L,S0) => input(S0) - L // FIXME is the "- L" not redundant?
	}
}

function glob(S : Statement) : set<Variable>
	ensures glob(S) == setOf(def(S) + input(S));
{
	set v | v in def(S) + input(S)
}

function setOf(s : seq<Variable>) : set<Variable>
{
	set x | x in s
}

function method coVarSeq(xs : seq<Variable>, ys : seq<Variable>) : seq<Variable>
{
	if xs == [] then [] else if xs[0] in ys then coVarSeq(xs[1..],ys) else [xs[0]] + coVarSeq(xs[1..],ys)
}

method DuplicateStatement(S : Statement, V : seq<Variable>) returns (result : Statement)
	//requires ToString(S) == "i,sum,prod := i+1,sum+i,prod*i;";
	requires V == ["sum"];
	//requires setOf(V) < setOf(def(S));
	ensures result == LocalDeclaration(["isum"]+["ii","iprod"]+["fsum"],SeqComp(SeqComp(SeqComp(SeqComp(
		SeqComp(Assignment(["isum"]+["ii","iprod"],V+["i","prod"]),S),Assignment(["fsum"],V)),Assignment(V+["i","prod"],["isum"]+["ii","iprod"])),S),Assignment(V,["fsum"])));
{
	var coV := ["i","prod"]; //coVarSeq(def(S),V);
	var iV := ["isum"]; // freshInit(V, allVars);
	var icoV := ["ii","iprod"]; //freshInit(coV, allVars);
	var fV := ["fsum"]; //freshInit(V, allVars);
	result := DS0(S,V,coV,iV,icoV,fV);
}

method DS0(S : Statement, V : seq<Variable>, coV : seq<Variable>, iV : seq<Variable>, icoV : seq<Variable>, fV : seq<Variable>) returns (result : Statement)
	//requires ToString(S) == "i,sum,prod := i+1,sum+i,prod*i;";
	requires V == ["sum"] && coV == ["i","prod"] && iV == ["isum"] && icoV == ["ii","iprod"] && fV == ["fsum"];
	requires |V| + |coV| + |iV| + |icoV| + |fV| == |V + coV + iV + icoV + fV|; // disjoint sets
	requires |V| == |iV| == |fV|;
	requires |coV| == |icoV|;
	requires setOf(def(S)) == setOf(V+coV);
	requires glob(S) == {"i","sum","prod"};
	requires setOf(iV) == {"isum"};
//	requires setOf(iV + icoV + fV) !! glob(S); // fresh variables
	ensures result == LocalDeclaration(iV+icoV+fV,SeqComp(SeqComp(SeqComp(SeqComp(
		SeqComp(Assignment(iV+icoV,V+coV),S),Assignment(fV,V)),Assignment(V+coV,iV+icoV)),S),Assignment(V,fV)));
{
	var S1 := DS1(S,V,coV,iV,icoV);
	assert S1 == Assignment(iV+icoV,V+coV);//ToString(result) == "isum,ii,iprod := sum,i,prod;";
	result := S1;
	assert result == Assignment(iV+icoV,V+coV);//ToString(result) == "isum,ii,iprod := sum,i,prod;";
	var S2 := DS2(S);
	assert S2 == S;
	result := SeqComp(result,S2);
	assert result == SeqComp(S1,S);
	var S3 := DS3(S,V,fV);
	assert S3 == Assignment(fV,V);
	result := SeqComp(result,S3);
	assert result == SeqComp(SeqComp(S1,S2),S3);
	var S4 := DS4(S,V,coV,iV,icoV);
	assert S4 == Assignment(V+coV,iV+icoV);
	result := SeqComp(result,S4);
	assert result == SeqComp(SeqComp(SeqComp(S1,S2),S3),S4);
	var S5 := DS5(S);
	assert S5 == S;
	result := SeqComp(result,S5);
	assert result == SeqComp(SeqComp(SeqComp(SeqComp(S1,S2),S3),S4),S5);
	var S6 := DS6(S,V,fV);
	assert S6 == Assignment(V,fV);
	result := SeqComp(result,S6);
	assert result == SeqComp(SeqComp(SeqComp(SeqComp(SeqComp(S1,S2),S3),S4),S5),S6);
	result := LocalDeclaration(iV+icoV+fV,result);
	assert result == LocalDeclaration(iV+icoV+fV,SeqComp(SeqComp(SeqComp(SeqComp(SeqComp(S1,S2),S3),S4),S5),S6));
}

method DS1(S : Statement, V : seq<Variable>, coV : seq<Variable>, iV : seq<Variable>, icoV : seq<Variable>) returns (result : Statement)
	//requires ToString(S) == "i,sum,prod := i+1,sum+i,prod*i;";
	requires V == ["sum"] && coV == ["i","prod"] && iV == ["isum"] && icoV == ["ii","iprod"];
	requires |V| + |coV| + |iV| + |icoV| == |V + coV + iV + icoV|; // disjoint sets
	requires |V| == |iV|;
	requires |coV| == |icoV|;
	requires setOf(def(S)) == setOf(V+coV);
	//requires (iV + icoV + fV) !! glob(S); // fresh variables
	//ensures ToString(result) == "isum,ii,iprod := sum,i,prod;";
	ensures result == Assignment(iV+icoV,V+coV);
{
	//result := "isum,ii,iprod := sum,i,prod;";
	assert iV+icoV == ["isum","ii","iprod"];
	assert V+coV == ["sum","i","prod"];
	//result := Assignment(iV+icoV,ExpressionsFromVariables(V+coV));
	result := Assignment(iV+icoV,V+coV);
}
/*
function method ExpressionsFromVariables(variables : seq<Variable>) : seq<Expression>
{
	if |variables| == 0 then [] else [variables[0]] + ExpressionsFromVariables(variables[1..])
}
*/
method DS2(S : Statement) returns (result : Statement)
	ensures result == S;
{
	result := S;
}

method DS3(S : Statement, V : seq<Variable>, fV : seq<Variable>) returns (result : Statement)
	//requires ToString(S) == "i,sum,prod := i+1,sum+i,prod*i;";
	//requires V == ["sum"] && fV == ["fsum"];
	requires |V| + |fV| == |V + fV|; // disjoint sets
	requires |V| == |fV|;
	ensures result == Assignment(fV,V);
{
	result := Assignment(fV,V);
}

method DS4(S : Statement, V : seq<Variable>, coV : seq<Variable>, iV : seq<Variable>, icoV : seq<Variable>) returns (result : Statement)
	//requires ToString(S) == "i,sum,prod := i+1,sum+i,prod*i;" && V == ["sum"] && coV == ["i","prod"] && iV == ["isum"] && icoV == ["ii","iprod"];
	requires |V| + |coV| + |iV| + |icoV| == |V + coV + iV + icoV|; // disjoint sets
	requires |V| == |iV|;
	requires |coV| == |icoV|;
	requires setOf(def(S)) == setOf(V+coV);
	//requires (iV + icoV) !! glob(S); // fresh variables
	ensures result == Assignment(V+coV,iV+icoV);
{
	result := Assignment(V+coV,iV+icoV);
}

method DS5(S : Statement) returns (result : Statement)
	ensures result == S;
{
	result := S;
}

method DS6(S : Statement, V : seq<Variable>, fV : seq<Variable>) returns (result : Statement)
	//requires ToString(S) == "i,sum,prod := i+1,sum+i,prod*i;" && V == ["sum"] && fV == ["fsum"];
	requires |V| + |fV| == |V + fV|; // disjoint sets
	requires |V| == |fV|;
	ensures result == Assignment(V,fV);
{
	result := Assignment(V,fV);
}

method FlowInsensitiveSliding(S : Statement, V : seq<Variable>) returns (result : Statement, SV: Statement, ScoV: Statement)
	//requires ToString(S) == "i,sum,prod := i+1,sum+i,prod*i;"
	requires V == ["sum"]
	//requires setOf(V) < setOf(def(S))
	ensures result == LocalDeclaration(["isum"]+["ii","iprod"]+["fsum"],SeqComp(SeqComp(SeqComp(SeqComp(
		SeqComp(Assignment(["isum"]+["ii","iprod"],V+["i","prod"]),SV),Assignment(["fsum"],V)),Assignment(V+["i","prod"],["isum"]+["ii","iprod"])),ScoV),Assignment(V,["fsum"])))
	ensures SV == FlowInsensitiveSlice(S,setOf(V))
	ensures ScoV == FlowInsensitiveSlice(S,def(S) - setOf(V))
{
	var coV := ["i","prod"]; //coVarSeq(def(S),V);
	var iV := ["isum"]; // freshInit(V, allVars);
	var icoV := ["ii","iprod"]; //freshInit(coV, allVars);
	var fV := ["fsum"]; //freshInit(V, allVars);
	SV := ComputeFISlice(S,setOf(V));
	ScoV := ComputeFISlice(S,setOf(coV));
	result := DS0(S,V,coV,iV,icoV,fV);
}

function FlowInsensitiveSlice(S: Statement, V: set<Variable>): Statement
	// FIXME: generalize
	requires S == Assignment(["i","sum", "prod"],["i+1","sum+i","prod*i"])
{
	if V == {"sum"} then Assignment(["sum"],["sum+i"])
	else Assignment(["i","prod"],["i+1","prod*i"])
}

method ComputeFISlice(S: Statement, V: set<Variable>) returns (SV: Statement)
	ensures SV == FlowInsensitiveSlice(S,V)
{
	// TODO: implement...
	 
}

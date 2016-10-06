datatype Statement = Assignment(LHS : seq<Variable>, RHS : seq<Expression>) | Skip | SeqComp(S1 : Statement, S2 : Statement) | 
		IF(B0 : BooleanExpression, Sthen : Statement, Selse : Statement) | DO(B : BooleanExpression, S : Statement) |
		LocalDeclaration(L : seq<Variable>, S0 : Statement)
type Variable = string
type Expression = string
type BooleanExpression = string

class VariablesSSA {

	var m: map<Variable, seq<Variable>>;
	var n: int;

	constructor ()
	{
		n := 1;
	}

	function getAndIncN() : int
	{
		incN();
		n - 1
	}

	method incN()
	{
		n := n + 1;
	}


	method variablesToSSAVariables(variables: seq<Variable>, instances: seq<Variable>)
	{
		if !(variables == []) { addVariable(variables[0], instances[0]); variablesToSSAVariables(variables[1..], instances[1..]); }
	}

	method addVariable(v: Variable, vSSA: Variable)
	{
		if v in m { m := m[v := m[v] + [vSSA]]; } else { m := m[v := [vSSA]]; }
	}

	method getVariableInRegularForm(vSSA: Variable)  returns (v : Variable)
	{
		v :| v in m && vSSA in m[v]; 
	}

	method instancesToVariables(instances: seq<Variable>) returns (V : seq<Variable>)
	{
		if instances == [] { V := []; } 
		else { 
			var v := getVariableInRegularForm(instances[0]);
			var V' := instancesToVariables(instances[1..]);

			V := [v] + V';
		}
	}

	method getInstancesOfVarible(v : Variable) returns (instances : seq<Variable>)
	{
		instances := m[v];
	}

	method getInstancesOfVaribleSeq(V : seq<Variable>) returns (instances : seq<Variable>)
	{
		if V == [] { instances := []; }
		else {
			var vInstaces := getInstancesOfVarible(V[0]);
			var instances' := getInstancesOfVaribleSeq(V[1..]);
			instances := vInstaces + instances';
		}
	}
}

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
	//assert S' == LocalDeclaration(["isum"]+["ii","iprod"]+["fsum"],SeqComp(SeqComp(SeqComp(SeqComp(
	//	SeqComp(Assignment(["isum"]+["ii","iprod"],V+["i","prod"]),SV),Assignment(["fsum"],V)),Assignment(V+["i","prod"],["isum"]+["ii","iprod"])),ScoV),Assignment(V,["fsum"])));
	//assert SV == Assignment(["sum"],["sum+i"]);
	//assert ScoV == Assignment(["i","prod"],["i+1","prod*i"]);
	result := ToString(ScoV);
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


 function method freshInit(vars : seq<Variable>, ghost allVars : set<Variable>, vsSSA : VariablesSSA) : seq<Variable>
	//requires |setOf(vars)| == |vars|;

	requires setOf(vars) < allVars;
	requires forall v :: v in vars ==> "i"+v !in allVars;
	ensures setOf(freshInit(vars,allVars,vsSSA)) !! allVars;
	ensures setOf(freshInit(vars,allVars,vsSSA)) !! allVars;
	ensures |freshInit(vars,allVars,vsSSA)| == |vars|;
{
	// if vars == [] then [] else ["i"+vars[0]] + freshInit(vars[1..],allVars+{"i"+vars[0]})

	var n := vsSSA.getAndIncN();

	if vars == [] then [] else [vars[0]+n] + freshInit(vars[1..], allVars + {vars[0]+n}, vsSSA)
}

function method def(S : Statement) : set<Variable> // FIXME: make it return a set
//	ensures def(S) == {"i","sum","prod"};
{
	match S {
		case Assignment(LHS,RHS) => setOf(LHS) // FIXME
		case Skip => {}
		case SeqComp(S1,S2) => def(S1) + def(S2)
		case IF(B0,Sthen,Selse) => def(Sthen) + def(Selse)
		case DO(B,S) => def(S)
		case LocalDeclaration(L,S0) => def(S0) - setOf(L)
	}
}

function method ddef(S : Statement) : set<Variable>
//	ensures ddef(S) == ["i","sum","prod"];
{
	match S {
		case Assignment(LHS,RHS) => setOf(LHS) // FIXME
		case Skip => {}
		case SeqComp(S1,S2) => ddef(S1) + ddef(S2)
		case IF(B0,Sthen,Selse) => ddef(Sthen) * ddef(Selse)
		case DO(B,S) => {}
		case LocalDeclaration(L,S0) => ddef(S0) - setOf(L)
	}
}

function method input(S : Statement) : set<Variable>
//	ensures input(S) == ["i","sum","prod"];
{
	match S {
		case Assignment(LHS,RHS) => setOf(LHS) // FIXME (LHS is a sequence of Expression(s), not Variable(s)
		case Skip => {}
		case SeqComp(S1,S2) => input(S1) + (input(S2) - ddef(S1)) // right?
		case IF(B0,Sthen,Selse) => setOf([B0]) + input(Sthen) + input(Selse) // FIXME: variables of B0?
		case DO(B,S) => setOf([B]) + input(S) // FIXME: variables of B?
		case LocalDeclaration(L,S0) => input(S0) - setOf(L) // FIXME is the "- L" not redundant?
	}
}

function method glob(S : Statement) : set<Variable>
	//ensures glob(S) == setOf(def(S) + input(S));
{
	set v | v in def(S) + input(S)
}

function method setOf(s : seq<Variable>) : set<Variable>
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
	//requires setOf(def(S)) == setOf(V+coV);
//	requires glob(S) == {"i","sum","prod"};
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
	//requires setOf(def(S)) == setOf(V+coV);
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
	//requires setOf(def(S)) == setOf(V+coV);
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
	//ensures result == LocalDeclaration(["isum"]+["ii","iprod"]+["fsum"],SeqComp(SeqComp(SeqComp(SeqComp(
	//	SeqComp(Assignment(["isum"]+["ii","iprod"],V+["i","prod"]),SV),Assignment(["fsum"],V)),Assignment(V+["i","prod"],["isum"]+["ii","iprod"])),ScoV),Assignment(V,["fsum"])))
	//ensures SV == FlowInsensitiveSlice(S,setOf(V))
	//ensures ScoV == FlowInsensitiveSlice(S,def(S) - setOf(V))
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
	//requires S == Assignment(["i","sum", "prod"],["i+1","sum+i","prod*i"])
{
	if V == {"sum"} then Assignment(["sum"],["sum+i"])
	else Assignment(["i","prod"],["i+1","prod*i"])
}

function method GetAssignmentsOfV(LHS : seq<Variable>, RHS : seq<Expression>, V: set<Variable>) : Statement
	//requires |LHS| == |RHS|
	ensures GetAssignmentsOfV(LHS, RHS, V).Assignment? || GetAssignmentsOfV(LHS, RHS, V).Skip?
	//ensures V * setOf(LHS) != {} ==> GetAssignmentsOfV(LHS, RHS, V).Assignment?
{
	if LHS == [] || RHS == [] then Skip
	else if LHS[0] in V then //assert V * setOf(LHS) != {};
	var tempRes := GetAssignmentsOfV(LHS[1..], RHS[1..], V);
	match tempRes {
		case Assignment(LHS1,RHS1) => Assignment([LHS[0]]+LHS1, [RHS[0]]+RHS1)
		case Skip => Assignment([LHS[0]], [RHS[0]])
	}
	else GetAssignmentsOfV(LHS[1..], RHS[1..], V)

	/*if LHS == [] then Skip
	else if LHS[0] in V then SeqComp(Assignment([LHS[0]],[RHS[0]]), GetAssignmentsOfV(LHS[1..], RHS[1..], V))
	else GetAssignmentsOfV(LHS[1..], RHS[1..], V)*/
}

function method ComputeSlides(S: Statement, V: set<Variable>) : Statement

{
	if V * def(S) == {} then Skip
	else
	match S {
		case Skip => Skip
		case Assignment(LHS,RHS) => GetAssignmentsOfV(LHS,RHS,V)
		case SeqComp(S1,S2) => SeqComp(ComputeSlides(S1,V), ComputeSlides(S2,V))
		case IF(B0,Sthen,Selse) => IF(B0, ComputeSlides(Sthen,V) , ComputeSlides(Selse,V))
		case DO(B,S) => DO(B, ComputeSlides(S,V))
		case LocalDeclaration(L,S0) => Skip
	}
}

function method ComputeSlidesDepRtc(S: Statement, V: set<Variable>) : set<Variable>
	decreases glob(S) - V
{
	var slidesSV := ComputeSlides(S, V);
	var U := glob(slidesSV) * def(S);

	if U <= V then V else ComputeSlidesDepRtc(S, V + U)
}


method ComputeFISlice(S: Statement, V: set<Variable>) returns (SV: Statement)
	//ensures SV == FlowInsensitiveSlice(S,V)
{
	var Vstar := ComputeSlidesDepRtc(S, V);

	SV := ComputeSlides(S, Vstar);
}

function method setToSeq(s : set<Variable>) : seq<Variable>
{
	var v :| v in s;

	if s == {} then [] else [v] + setToSeq(s - {v})
}

method ToSSA(S: Statement, X: seq<Variable>, liveOnEntryX: seq<Variable>, liveOnExitX: seq<Variable>, Y: set<Variable>, XLs: set<Variable>) returns(S': Statement)
{
	var vsSSA := new VariablesSSA();

	match S {
		case Assignment(LHS,RHS) => S' := AssignmentToSSA(LHS, RHS, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);
		case SeqComp(S1,S2) => S' := SeqCompToSSA(S1, S2, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);
		case IF(B0,Sthen,Selse) => S' := IfToSSA(B0, Sthen, Selse, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);
		case DO(B,S) => S' := DoToSSA(B, S, X, liveOnEntryX, liveOnExitX, Y, XLs, vsSSA);
	}
}

method IsVariableInSet(v: Variable, X: set<Variable>) returns (isInSet: bool)
{
	var x :| x in X;

	if X == {} { isInSet := false; }
	else if x == v { isInSet := true; }
	else
	{
		 isInSet := IsVariableInSet(v, X - {x});
	}
}

method GetXandE(LHS: seq<Variable>, RHS: seq<Expression>, X: set<Variable>) returns (XSeq: seq<Variable>, ESeq: seq<Expression>)
{
	if LHS == [] { XSeq:= []; ESeq := []; }
	else
	{
		var x, e := [], [];
		var isVariableInSet := IsVariableInSet(LHS[0], X);
		
		if isVariableInSet == true
		{
			x := [LHS[0]];
			e := [RHS[0]];
		}

		var XSeq', ESeq' := GetXandE(LHS[1..], RHS[1..], X);

		XSeq := x + XSeq';
		ESeq := e + ESeq';
	}

	// Reverse?
}

method InstancesSetToSeq(instancesOfX: set<Variable>, X: seq<Variable>, vsSSA: VariablesSSA) returns (instancesOfXSeq: seq<Variable>)
{
	// For example: instancesOfX	= {b2,a3,c1}
	//				X				= [a,b,c]
	//				instancesOfXSeq = [a3,b2,c1]	

	if X == [] { instancesOfXSeq := []; }
	else
	{
		var instances := vsSSA.getInstancesOfVarible(X[0]);					// instances = [a1,a2,a3,a4,...]
		var instanceOfX :| instanceOfX in setOf(instances) * instancesOfX;	// setOf(instances) * instancesOfX = {a1,a2,a3,a4,...} * {b2,a3,c1} = {a3}
		var instancesOfXSeq' := InstancesSetToSeq(instancesOfX, X[1..], vsSSA);			// instancesOfXSeq = [b2,c1]
		
		instancesOfXSeq := [instanceOfX] + instancesOfXSeq';				// instancesOfXSeq = [a3,b2,c1]
	}
}

method SubstitueExpressionSeq(E: seq<Expression>, X: seq<set<Variable>>, XLi: seq<set<Variable>>) returns (E': seq<Expression>)
{
	// TODO - OR!
}

method SubstitueBooleanExpression(B: BooleanExpression, X: seq<set<Variable>>, XLi: seq<set<Variable>>) returns (B': BooleanExpression)
{
	// TODO - OR!
}

method AssignmentToSSA(LHS: seq<Variable>, RHS: seq<Expression>, X: seq<Variable>, liveOnEntryX: seq<Variable>, liveOnExitX: seq<Variable>, Y: set<Variable>, XLs: set<Variable>, vsSSA: VariablesSSA) returns (S': Statement)
{
	// defined in thesis:
	// toSSA.("X4,X2,X5,X6,Y1 := E1,E2,E3,E4,E5",
	// X, (XL1i, XL2i, XL3i, XL4i), (XL3i, XL4f ,XL5f), Y ,XLs)) is:
	// "XL4f, XL2, XL5f, XL6, Y1 := E1', E2', E3', E4', E5'"

	//// find X1,X2,X3,X4,X5,X6,Y1 SETS ////

	var XL3i := setOf(liveOnEntryX) * setOf(liveOnExitX);
	var X3Seq := vsSSA.instancesToVariables(setToSeq(XL3i));
	var X3 := setOf(X3Seq);

	var XL1iXL2iXL4i := setOf(liveOnEntryX) - XL3i;
	var X1X2X4 := vsSSA.instancesToVariables(setToSeq(XL1iXL2iXL4i));
	var XL4fXL5f := setOf(liveOnExitX) - XL3i;
	var X4X5 := vsSSA.instancesToVariables(setToSeq(XL4fXL5f));
	var X4 := setOf(X1X2X4) * setOf(X4X5);
	var X5 := setOf(X4X5) - X4;

	var X1X2 := setOf(X1X2X4) - X4;
	var X2 := X1X2 * def(Assignment(LHS,RHS));
	var X1 := X1X2 - X2;

	var X6Y1 := setOf(liveOnEntryX) - X4 - X2 - X5;
	var X6 := setOf(X) * X6Y1;
	var Y1 := X6Y1 - X6;

	////////////////////////////////////////

	var E1, E2, E3, E4, E5;
	var X4Seq, X2Seq, X5Seq, X6Seq, Y1Seq;

	X4Seq, E1 := GetXandE(LHS, RHS, X4);
	X2Seq, E2 := GetXandE(LHS, RHS, X2);
	X5Seq, E3 := GetXandE(LHS, RHS, X5);
	X6Seq, E4 := GetXandE(LHS, RHS, X6);
	Y1Seq, E5 := GetXandE(LHS, RHS, Y1);
	
	////////////////////////////////////////

	var X4Instances := vsSSA.getInstancesOfVaribleSeq(X4Seq);
	var XL5f := XL4fXL5f - setOf(X4Instances);
	var XL4f := XL4fXL5f - XL5f;

	var XL5fSeq := InstancesSetToSeq(XL5f, X5Seq, vsSSA);
	var XL4fSeq := InstancesSetToSeq(XL4f, X4Seq, vsSSA);

	////////////////////////////////////////

	var E1', E2', E3', E4', E5';
	var XL1iXL2i := XL1iXL2iXL4i - setOf(X4Instances);
	var XL4i := XL1iXL2iXL4i - XL1iXL2i;

	var X2Instances := vsSSA.getInstancesOfVaribleSeq(X2Seq);
	var XL1i := XL1iXL2i - setOf(X2Instances);
	var XL2i := XL1iXL2i - XL1i;

	E1' := SubstitueExpressionSeq(E1, [X1,X2,X3,X4], [XL1i,XL2i,XL3i,XL4i]);
	E2' := SubstitueExpressionSeq(E2, [X1,X2,X3,X4], [XL1i,XL2i,XL3i,XL4i]);
	E3' := SubstitueExpressionSeq(E3, [X1,X2,X3,X4], [XL1i,XL2i,XL3i,XL4i]);
	E4' := SubstitueExpressionSeq(E4, [X1,X2,X3,X4], [XL1i,XL2i,XL3i,XL4i]);
	E5' := SubstitueExpressionSeq(E5, [X1,X2,X3,X4], [XL1i,XL2i,XL3i,XL4i]);

	var XL2XL6 := freshInit(X2Seq + X6Seq, setOf(X)+Y+XLs, vsSSA);
		 
		vsSSA.variablesToSSAVariables(X2Seq + X6Seq, XL2XL6);

	////////////////////////////////////////
	
	var LHS' := XL4fSeq + XL2XL6[..|X2|] + XL5fSeq + XL2XL6[|X2|..] + Y1Seq;
	var RHS' := E1' + E2' + E3' + E4' + E5';

	S' := Assignment(LHS', RHS');
}

method SeqCompToSSA(S1: Statement, S2: Statement, X: seq<Variable>, liveOnEntryX: seq<Variable>, liveOnExitX: seq<Variable>, Y: set<Variable>, XLs: set<Variable>, vsSSA: VariablesSSA) returns (S': Statement)
{
	// defined in thesis:
	// toSSA.(" S1 ; S2 ", X, (XL1i, XL2i, XL3i, XL4i), (XL3i, XL4f, XL5f), Y, XLs) is:
	// " S1' ; S2' "
	
	var XL3i := setOf(liveOnEntryX) * setOf(liveOnExitX);
	var X3Seq := vsSSA.instancesToVariables(setToSeq(XL3i));
	var X3 := setOf(X3Seq);

	var liveOnEntryXVariables := vsSSA.instancesToVariables(liveOnEntryX);
	var liveOnExitXVariables := vsSSA.instancesToVariables(liveOnExitX);
	var X3X4 := setOf(liveOnEntryXVariables) * setOf(liveOnExitXVariables);
	var X4 := X3X4 - X3;
	var X5 := setOf(liveOnExitXVariables) - X3X4;

	var X1X2 := setOf(liveOnEntryXVariables) - X3X4;
	var X2 := X1X2 * (def(S1) + def(S2));
	var X1 := X1X2 - X2;

	var XL1iXL2iXL4i := setOf(liveOnEntryX) - XL3i;
	var X4Instances := vsSSA.getInstancesOfVaribleSeq(setToSeq(X4));
	var XL1iXL2i := XL1iXL2iXL4i - setOf(X4Instances);
	var XL4i := XL1iXL2iXL4i - XL1iXL2i;

	var X2Instances := vsSSA.getInstancesOfVaribleSeq(setToSeq(X2));
	var XL1i := XL1iXL2i - setOf(X2Instances);
	var XL2i := XL1iXL2i - XL1i;

	var XL4fXL5f := setOf(liveOnExitX) - XL3i;
	var XL5f := XL4fXL5f - setOf(X4Instances);
	var XL4f := XL4fXL5f - XL5f;

	var X6 := (setOf(X) - X3) * (((X4 + X5) - ddef(S2)) + input(S2)); 
	var X11 := X1 * X6; 
	var X21 := (X2 * X6) - def(S1); 
	var X41 := (X4 * X6) - def(S1); 
	var X42 := (X4 * X6) - def(S2); 
	var X51 := (X5 * X6) - def(S2);
	var X61 := X6 - (X11+X21+X41+X42+X51); 

	var X61Seq := setToSeq(X61);
	var XL61Seq := freshInit(X61Seq, setOf(X) + Y + XLs, vsSSA);
		
		vsSSA.variablesToSSAVariables(X61Seq, XL61Seq);

	var XL11iTemp := vsSSA.getInstancesOfVaribleSeq(setToSeq(X1));
	var XL11iSeq := setToSeq(setOf(XL11iTemp) * XL1i);
	var XL21iTemp := vsSSA.getInstancesOfVaribleSeq(setToSeq(X2));
	var XL21iSeq := setToSeq(setOf(XL21iTemp) * XL2i);
	var XL41iTemp := vsSSA.getInstancesOfVaribleSeq(setToSeq(X4));
	var XL41iSeq := setToSeq(setOf(XL11iTemp) * XL4i);
	var XL42fTemp := vsSSA.getInstancesOfVaribleSeq(setToSeq(X4));
	var XL42fSeq := setToSeq(setOf(XL11iTemp) * XL4f);
	var XL51fTemp := vsSSA.getInstancesOfVaribleSeq(setToSeq(X5));
	var XL51fSeq := setToSeq(setOf(XL11iTemp) * XL5f);
	var XL6 := XL11iSeq + XL21iSeq + setToSeq(XL3i) + XL41iSeq + XL42fSeq + XL51fSeq + XL61Seq;

	var XLs' := XLs + setOf(XL61Seq);
	var S1' := ToSSA(S1, X, liveOnEntryX, XL6, Y, XLs');
	var XLs'' := XLs' + (glob(S1') - Y);
	var S2' := ToSSA(S2, X, XL6, liveOnExitX, Y, XLs'');

	S' := SeqComp(S1', S2');
}

method FindVariableIndexInVariableSequence(v: Variable, V: seq<Variable>) returns (i: int)
{
	if V[0] == v { i := 0; }
	else
	{
		i := FindVariableIndexInVariableSequence(v, V[1..]);
		i := i + 1;
	}
}

method OrganizeVariables(vars1: seq<Variable>, vars2: seq<Variable>, vsSSA: VariablesSSA) returns (res: seq<Variable>)
{
	if vars1 == [] { res := []; }
	else
	{
		var v1 := vsSSA.getVariableInRegularForm(vars1[0]);
		var vars2Variables := vsSSA.instancesToVariables(vars2);
		var index := FindVariableIndexInVariableSequence(v1, vars2Variables);
		var res' := OrganizeVariables(vars1[1..], vars2, vsSSA);

		res := [vars2[index]] + res';
	}
}

method IfToSSA(B : BooleanExpression, S1 : Statement, S2 : Statement, X: seq<Variable>, liveOnEntryX: seq<Variable>, liveOnExitX: seq<Variable>, Y: set<Variable>, XLs: set<Variable>, vsSSA: VariablesSSA) returns (S': Statement)
{
	// defined in thesis:
	// toSSA.(IF ,X, (XL1i, XL2i, XL3i, XL4i), (XL3i, XL4f, XL5f), Y, XLs) is:
	// IF' where:
	// IF := " if B then S1 else S2 fi "
	// IF' := " if B' then S1'; XL4f ,XL5f := XL4t, XL5t else S2'; XL4f ,XL5f := XL4e, XL5e fi "

	var XL3i := setOf(liveOnEntryX) * setOf(liveOnExitX);
	var X3Seq := vsSSA.instancesToVariables(setToSeq(XL3i));
	var X3 := setOf(X3Seq);

	var XL4fXL5f := setOf(liveOnExitX) - XL3i;
	var X4X5 := vsSSA.instancesToVariables(setToSeq(XL4fXL5f));
	var liveOnEntryXVariables := vsSSA.instancesToVariables(liveOnEntryX);
	var X4 := setOf(liveOnEntryXVariables) * setOf(X4X5);
	var X5Seq := setToSeq(setOf(X4X5) - X4);

	var X2 := (setOf(liveOnEntryXVariables) - X4) * (def(S1) + def(S2));
	var X1 := setOf(liveOnEntryXVariables) - X4 - X3 - X2;

	var XL1iXL2iXL4i := setOf(liveOnEntryX) - XL3i;
	var X4Instances := vsSSA.getInstancesOfVaribleSeq(setToSeq(X4));
	var XL1iXL2i := XL1iXL2iXL4i - setOf(X4Instances);
	var XL4i := XL1iXL2iXL4i - XL1iXL2i;

	var X2Instances := vsSSA.getInstancesOfVaribleSeq(setToSeq(X2));
	var XL1i := XL1iXL2i - setOf(X2Instances);
	var XL2i := XL1iXL2i - XL1i;

	var B' := SubstitueBooleanExpression(B, [X1,X2,X3,X4], [XL1i,XL2i,XL3i,XL4i]);
	
	var X4d1 := X4 * (def(S1) - def(S2));
	var X4d2 := X4 * (def(S2) - def(S1));
	var X4d1d2 := X4 * def(S1) * def(S2);

	var variables := setToSeq(X4d1) + setToSeq(X4d2) + setToSeq(X4d1d2) + setToSeq(X4d1d2) + X5Seq + X5Seq;
	var instances := freshInit(variables, setOf(X) + Y + XLs, vsSSA);

		vsSSA.variablesToSSAVariables(variables, instances);

	var XL4d1t := instances[0..|X4d1|];
	var XL4d2iTemp := vsSSA.getInstancesOfVaribleSeq(setToSeq(X4d2));
	var XL4d2iSeq := setToSeq(setOf(XL4d2iTemp) * XL4i);
	var XL4d1d2t := instances[|X4d1|+|X4d2|..|X4d1|+|X4d2|+|X4d1d2|];
	var XL4t := XL4d1t + XL4d2iSeq + XL4d1d2t;

	var XL4d1iTemp := vsSSA.getInstancesOfVaribleSeq(setToSeq(X4d1));
	var XL4d1iSeq := setToSeq(setOf(XL4d1iTemp) * XL4i);
	var XL4d2e := instances[|X4d1|..|X4d2|];
	var XL4d1d1e := instances[|X4d1|+|X4d2|+|X4d1d2|..|X4d1|+|X4d2|+|X4d1d2|+|X4d1d2|];
	var XL4e := XL4d1iSeq + XL4d2e + XL4d1d1e;

	var XL5t := instances[|instances|-|X5Seq|-|X5Seq|..|instances|-|X5Seq|];
	var XL5e := instances[|instances|-|X5Seq|..|instances|];

	var XL5f := XL4fXL5f - setOf(X4Instances);
	var XL5fSeq := OrganizeVariables(XL5t, setToSeq(XL5f), vsSSA);
	var XL4f := XL4fXL5f - XL5f;
	var XL4fSeqThen := OrganizeVariables(XL4t, setToSeq(XL4f), vsSSA);
	var XL4fSeqElse := OrganizeVariables(XL4e, setToSeq(XL4f), vsSSA);

	var XLs' := XLs + setOf(instances);
	var S1' := ToSSA(S1, X, liveOnEntryX, (setToSeq(XL3i) + XL4t + XL5t), Y, XLs');
	var XLs'' := XLs' + (glob(S1') - Y);
	var S2' := ToSSA(S2, X, liveOnEntryX, (setToSeq(XL3i) + XL4e + XL5e), Y, XLs'');

	S' := IF(B', SeqComp(S1', Assignment(XL4fSeqThen + XL5fSeq, XL4t + XL5t)), SeqComp(S2', Assignment(XL4fSeqElse + XL5fSeq, XL4e + XL5e)));
}

method DoToSSA(B : BooleanExpression, S : Statement, X: seq<Variable>, liveOnEntryX: seq<Variable>, liveOnExitX: seq<Variable>, Y: set<Variable>, XLs: set<Variable>, vsSSA: VariablesSSA) returns (S'': Statement)
{
	// defined in thesis:
	// toSSA.(DO, X, (XL1i, XL2i, XL3i, XL4i), (XL3i, XL4f), Y ,XLs) is:
	// "XL2, XL4f := XL2i, XL4i; DO'" where:
	// DO := " while B do S1 od ",
	// DO' := " while B' do S1'; XL2, XL4f := XL2b, XL4b od "

	var XL4f := setOf(liveOnExitX) - (setOf(liveOnEntryX) * setOf(liveOnExitX));
	var XL4fSeq := setToSeq(XL4f);
	var X4Seq := vsSSA.instancesToVariables(setToSeq(XL4f));
	var X4 := setOf(X4Seq);

	var liveOnEntryXVariables := vsSSA.instancesToVariables(liveOnEntryX);
	var X2 := (setOf(liveOnEntryXVariables) - X4) * def(S);
	var X2Seq := setToSeq(X2);

	var XL3i := setOf(liveOnEntryX) * setOf(liveOnExitX);
	var XL3iSeq := setToSeq(XL3i);
	var X3Seq := vsSSA.instancesToVariables(XL3iSeq);
	var X3 := setOf(X3Seq);
	
	var X1 := setOf(liveOnEntryXVariables) - X4 - X3 - X2;

	var variables := X2Seq + X2Seq + X4Seq;
	var instances := freshInit(variables, setOf(X) + Y + XLs, vsSSA);

		vsSSA.variablesToSSAVariables(variables, instances);

	var XL2Seq := instances[0..|X2|];
	var XL2bSeq := instances[|X2|..|X2|+|X2|];
	var XL4bSeq := instances[|X2|+|X2|..];

	var XL1iXL2iXL4i := setOf(liveOnEntryX) - (setOf(liveOnEntryX) * setOf(liveOnExitX));
	var X4Instances := vsSSA.getInstancesOfVaribleSeq(X4Seq);
	var XL1iXL2i := XL1iXL2iXL4i - setOf(X4Instances);
	var XL4i := XL1iXL2iXL4i - XL1iXL2i;
	var XL4iSeq := OrganizeVariables(XL4fSeq, setToSeq(XL4i), vsSSA);

	var X2Instances := vsSSA.getInstancesOfVaribleSeq(X2Seq);
	var XL1i := XL1iXL2i - setOf(X2Instances);
	var XL2i := XL1iXL2i - XL1i;
	var XL2iSeq := OrganizeVariables(XL2Seq, setToSeq(XL2i), vsSSA);
	
	////////////////////////////////////////

	var XLs' := XLs + setOf(instances);
	var B' := SubstitueBooleanExpression(B, [X1,X2,X3,X4], [XL1i,setOf(XL2Seq),XL3i,XL4f]);
	var S' := ToSSA(S, X, (setToSeq(XL1i) + XL2Seq + XL3iSeq + XL4fSeq), (setToSeq(XL1i) + XL2bSeq + XL3iSeq + XL4bSeq), Y, XLs');
	var DO' := SeqComp(DO(B', S'), Assignment(XL2Seq + XL4fSeq, XL2bSeq + XL4bSeq));

	S'' := SeqComp(Assignment(XL2Seq + XL4fSeq, XL2iSeq + XL4iSeq), DO');
}





method FromSSA(S': Statement, X: seq<Variable>, XL1i: seq<Variable>, XL2f: seq<Variable>, Y: set<Variable>, XLs: set<Variable>) returns( S: Statement)
{
	S := MergeVars(S', XLs, X, XL1i, XL2f, Y);
}

method MergeVars(S': Statement, XLs: set<Variable>, X: seq<Variable>, XL1i: seq<Variable>, XL2f: seq<Variable>, Y: set<Variable>) returns( S: Statement)
{
	var vsSSA := new VariablesSSA();

	match S' {
		case Assignment(LHS,RHS) => S := AssignmentFromSSA(LHS, RHS, XLs, X, XL1i, XL2f, Y, vsSSA);
		case SeqComp(S1',S2') => S := SeqCompFromSSA(S1', S2', XLs, X, XL1i, XL2f, Y, vsSSA);
		case IF(B0,Sthen,Selse) => S := IfFromSSA(B0, Sthen, Selse, XLs, X, XL1i, XL2f, Y, vsSSA);
		case DO(B,S') => S := DoFromSSA(B, S', XLs, X, XL1i, XL2f, Y, vsSSA);
	}
}

method AssignmentFromSSA(LHS: seq<Variable>, RHS: seq<Variable>, XLs: set<Variable>, X: seq<Variable>, XLi: seq<Variable>, XLf: seq<Variable>, Y: set<Variable>, vsSSA: VariablesSSA) returns (S: Statement)
{
	// defined in thesis:
	// merge-vars.(" XL1f,XL2,XL3f,XL4,XL5f,XL6,Y1 := XL1i,XL2i,E1',E2',E3',E4',E5' ",
	// XLs, X, (XL1i, XL2i, XL3i, XL4i, XL7i, XL8i), (XL1f, XL3f, XL5f, XL7i), Y) is:
	// " X3,X4,X5,X6,Y1 := E1,E2,E3,E4,E5 "

	var Y1 := Y * def(Assignment(LHS, RHS)); // Y1 חיתוך בין Y ל def
	var Y1Seq, E5' := GetXandE(LHS, RHS, Y1);

	var XL7i := setOf(XLi) * setOf(XLf);
	var X7Seq := vsSSA.instancesToVariables(setToSeq(XL7i));
	var X7 := setOf(X7Seq);

	var XL1iXL2i := setOf(XLi) * setOf(RHS);
	var X1X2 := vsSSA.instancesToVariables(setToSeq(XL1iXL2i));
	var XL3iXL4iXL8i := setOf(XLi) - XL1iXL2i - XL7i;
	var X3X4X8 := vsSSA.instancesToVariables(setToSeq(XL3iXL4iXL8i));
	var XL1fXL3fXL5f := setOf(XLf) - XL7i;
	var X1X3X5 := vsSSA.instancesToVariables(setToSeq(XL1fXL3fXL5f));

	var X3 := setOf(X1X3X5) * setOf(X3X4X8);
	var X3Instances := vsSSA.getInstancesOfVaribleSeq(setToSeq(X3));
	var XL3fSeq, E1' := GetXandE(LHS, RHS, setOf(X3Instances));

	var XL1fXL5f := XL1fXL3fXL5f - setOf(XL3fSeq);
	var X1X5 := vsSSA.instancesToVariables(setToSeq(XL1fXL5f));
	var X1 := setOf(X1X2) * setOf(X1X5);
	var X1Instances := vsSSA.getInstancesOfVaribleSeq(setToSeq(X1));
	var XL1i := setOf(RHS) * setOf(X1Instances);
	var XL1f := setOf(LHS) * setOf(X1Instances);
	var XL5f := XL1fXL5f - XL1f;
	var XL5fSeq, E3' := GetXandE(LHS, RHS, XL5f);
	var X5SeqTemp := vsSSA.instancesToVariables(XL5fSeq);
	var X5 := setOf(X5SeqTemp);

	var XL2XL4XL6 := setOf(LHS) - XL1f - setOf(XL3fSeq) - XL5f - Y1;
	var XL2i := XL1iXL2i - XL1i;
	var X2 := setOf(X1X2) - X1;
	var X2Instances := vsSSA.getInstancesOfVaribleSeq(setToSeq(X2));
	var XL2 := setOf(RHS) * setOf(X2Instances);
	var XL4XL6 := XL2XL4XL6 - XL2;
	var X4X6 := vsSSA.instancesToVariables(setToSeq(XL4XL6));
	var X4 := setOf(X3X4X8) * setOf(X4X6);
	var X6 := setOf(X4X6) - X4;
	var X4Instances := vsSSA.getInstancesOfVaribleSeq(setToSeq(X4));
	var XL4 := setOf(X4Instances) * setOf(LHS);
	var XL6 := XL4XL6 - XL4;
	var XL4Seq, E2' := GetXandE(LHS, RHS, XL4);
	var XL6Seq, E4' := GetXandE(LHS, RHS, XL6);

	var X8 := setOf(X3X4X8) - X3 - X4;
	var XL3i := setOf(X3Instances) * setOf(XLi);
	var XL4i := setOf(X4Instances) * setOf(XLi);
	var XL8i := XL3iXL4iXL8i - XL3i - XL4i;

	////////////////////////////////////////

	var X3Seq := InstancesSetToSeq(X3, XL3fSeq, vsSSA);
	var X4Seq := InstancesSetToSeq(X4, XL4Seq, vsSSA);
	var X5Seq := InstancesSetToSeq(X5, XL5fSeq, vsSSA);
	var X6Seq := InstancesSetToSeq(X6, XL6Seq, vsSSA);

	////////////////////////////////////////

	var E1, E2, E3, E4, E5;

	E1 := SubstitueExpressionSeq(E1', [XL1i, XL2i, XL3i, XL4i, XL7i, XL8i], [X1, X2, X3, X4, X7, X8]);
	E2 := SubstitueExpressionSeq(E2', [XL1i, XL2i, XL3i, XL4i, XL7i, XL8i], [X1, X2, X3, X4, X7, X8]);
	E3 := SubstitueExpressionSeq(E3', [XL1i, XL2i, XL3i, XL4i, XL7i, XL8i], [X1, X2, X3, X4, X7, X8]);
	E4 := SubstitueExpressionSeq(E4', [XL1i, XL2i, XL3i, XL4i, XL7i, XL8i], [X1, X2, X3, X4, X7, X8]);
	E5 := SubstitueExpressionSeq(E5', [XL1i, XL2i, XL3i, XL4i, XL7i, XL8i], [X1, X2, X3, X4, X7, X8]);

	S := Assignment(X3Seq + X4Seq + X5Seq + X6Seq + Y1Seq, E1 + E2 + E3 + E4 + E5);
}

method SeqCompFromSSA(S1': Statement, S2': Statement, XLs: set<Variable>, X: seq<Variable>, XLi: seq<Variable>, XLf: seq<Variable>, Y: set<Variable>, vsSSA: VariablesSSA) returns (S: Statement)
{
	// defined in thesis:
	// merge-vars.(" S1' ; S2' ", XLs, X, XL1i, XL2f, Y) is:
	// " merge-vars.(S1', XLs, X, XL1i, XL3, Y) ; merge-vars.(S2', XLs, X, XL3, XL2f, Y) "

	var XL3 := XLs * ((setOf(XLf) - ddef(S2')) + input(S2'));
	var XL3Seq := setToSeq(XL3);

	var S1 := MergeVars(S1', XLs, X, XLi, XL3Seq, Y);
	var S2 := MergeVars(S2', XLs, X, XL3Seq, XLf, Y);

	S := SeqComp(S1, S2);
}

method IfFromSSA(B' : BooleanExpression, S1' : Statement, S2' : Statement, XLs: set<Variable>, X: seq<Variable>, XLi: seq<Variable>, XLf: seq<Variable>, Y: set<Variable>, vsSSA: VariablesSSA) returns (S: Statement)
{
	// defined in thesis:
	// merge-vars.(" if B' then S1' else S2' fi ", XLs, X, XL1i, XL2f, Y) is:
	// " if B' then merge-vars.(S1', XLs, X, XL1i, XL2f ,Y) else merge-vars.(S2', XLs, X, XL1i, XL2f, Y) fi "

	var X1 := {};
	var B := SubstitueBooleanExpression(B', [X1], [setOf(XLi)]);

	var S1 := MergeVars(S1', XLs, X, XLi, XLf, Y);
	var S2 := MergeVars(S2', XLs, X, XLi, XLf, Y);

	S := IF(B, S1, S2);
}

method DoFromSSA(B' : BooleanExpression, S' : Statement, XLs: set<Variable>, X: seq<Variable>, XLi: seq<Variable>, XLf: seq<Variable>, Y: set<Variable>, vsSSA: VariablesSSA) returns (S: Statement)
{
	// defined in thesis:
	// merge-vars.(" while B' do S1' od ", XLs, X, (XL1i, XL2i), XL2i, Y) is:
	// " while B' do merge-vars.(S1', XLs, X, (XL1i, XL2i), (XL1i, XL2i), Y) od "

	var XL2i := setOf(XLi) * setOf(XLf);
	var XL1i := setOf(XLi) - XL2i;
	var X1 := {}; // TODO
	var X2 := {}; // TODO
	var B := SubstitueBooleanExpression(B', [X1,X2], [XL1i,XL2i]);

	S := MergeVars(S', XLs, X, XLi, XLi, Y);
	S := DO(B, S);
}
(* ::Package:: *)

(* ::Title:: *)
(*QITools package: QuantumInformation*)


(* ::Text:: *)
(*A package with quantum information theory tools for Mathematica *)
(*\[Copyright] 2010-2015 Mart\[IAcute] Cuquet*)
(*https://github.com/mcuquet/QITools*)


(* ::Subtitle:: *)
(*License*)


(* ::Text:: *)
(*This file is part of the QITools package.*)
(*The QITools package is free software: you can redistribute it and/or modify it under*)
(*the terms of the GNU General Public License as published by the Free Software*)
(*Foundation, either version 3 of the License, or (at your option) any later*)
(*version.*)
(**)
(*This program is distributed in the hope that it will be useful, but WITHOUT*)
(*ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS*)
(*FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.*)
(**)
(*You should have received a copy of the GNU General Public License along with*)
(*this program. If not, see <http://www.gnu.org/licenses/>.*)


(* ::Subtitle:: *)
(*Functions*)


(* ::Section::Closed:: *)
(*BeginPackage*)


BeginPackage["QITools`QuantumInformation`"];


(* ::Section::Closed:: *)
(*Bras and kets*)


BraKet::usage = "BraKet[u,v] returns \[LeftAngleBracket]u|v\[RightAngleBracket]. BraKet[u,X,v] returns \[LeftAngleBracket]u|X|v\[RightAngleBracket]";
KetBra::usage = "KetBra[u,v] returns |u\[RightAngleBracket]\[LeftAngleBracket]v|. KetBra[u] returns |u\[RightAngleBracket]\[LeftAngleBracket]u|.";

Begin["`Private`"];

BraKet[u_,v_] := Conjugate[u].v;
BraKet[u_,X_,v_] := Conjugate[u].X.v;

KetBra[u_,v_] := Outer[Times,u,Conjugate[v]];
KetBra[u_] := KetBra[u,u];

End[];


(* ::Section::Closed:: *)
(*Commutators*)


AntiCommutator::usage = "AntiCommutator[A,B] returns A B + B A";
Commutator::usage = "Commutator[A,B] returns A B - B A";

Begin["`Private`"];

(* From QItoolbox *)
AntiCommutator[A_?MatrixQ,B_?MatrixQ] := A.B+B.A
Commutator[A_?MatrixQ,B_?MatrixQ] := A.B-B.A

End[];


(* ::Section:: *)
(*Entanglement measures and monotones*)


(* ::Subsection::Closed:: *)
(*Bipartite*)


Concurrence::usage = "ConcurrenceQubits[\[Psi]] gives the concurrence of the state \[Psi].
Concurrence[\[Rho]] gives the concurrence of the density matrix \[Rho].";
MaximumConversionProbabilityBipartite::usage = "MaximumConversionProbabilityBipartite[\[Psi],\[Phi],{da,db}] and MaximumConversionProbabilityBipartite[\[Psi],\[Phi],sys,dim] gives the maximum probability of the conversion \[Psi]->\[Phi] for the bipartite states \[Psi] and \[Phi].";
Negativity::usage = "Negativity[\[Rho]_,dims_List,part_List], Negativity[\[Rho]_,part_List] gives the negativity of state \[Rho]. See the description of PartialTranspose for more details regaring dim and part.";
PureQ::usage = "PureQ[\[Rho]] returns True if \[Rho] is pure, False otherwise.";
SchmidtCoefficients::usage = "SchmidtCoefficients[\[Psi],{da,db}] returns the Schmidt coefficients of the bipartite state \[Psi] of dimension da x db.
SchmidtCoefficients[\[Psi],sys,dim] returns the Schmidt coefficients of with respect to the bipartition of subsystems sys of a state \[Psi] with subsystem diemnsions d.";

Begin["`Private`"];

Concurrence[\[Psi]_?VectorQ] := 2Abs[Det[Partition[\[Psi],2]]]
Concurrence[\[Rho]_?MatrixQ] := Module[
	{
	\[Rho]t = \!\(
\*UnderoverscriptBox[\(\[Sum]\), \(i = 0\), \(3\)]\(
\*UnderoverscriptBox[\(\[Sum]\), \(j = 0\), \(3\)]KetBra[MagicState[i], MagicState[j]] . \[Rho] . KetBra[MagicState[i], MagicState[j]]\)\),
	\[Lambda]1,\[Lambda]2,\[Lambda]3,\[Lambda]4
	},

	{\[Lambda]1,\[Lambda]2,\[Lambda]3,\[Lambda]4} = Sort[
		Chop[Sqrt[Eigenvalues[(\[Rho].\[Rho]t)//FullSimplify]]]
		,FullSimplify[#1>#2]&
	];

	FullSimplify[Max[0,\[Lambda]1-\[Lambda]2-\[Lambda]3-\[Lambda]4]]
]

MaximumConversionProbabilityBipartite[\[Psi]_,\[Phi]_,{da_,db_}]:=Module[
{
\[Alpha]s=Sort[SchmidtCoefficients[\[Psi],{da,db}]//Chop,Greater],
\[Beta]s=Sort[SchmidtCoefficients[\[Phi],{da,db}]//Chop,Greater]
},

Min[Total[(\[Alpha]s^2)[[#;;]]]/Total[(\[Beta]s^2)[[#;;]]]&/@Range[Length[Cases[\[Beta]s,Except[0]]]]]
]
MaximumConversionProbabilityBipartite[\[Psi]_,\[Phi]_,sys_,dim_]:=Module[
{
\[Alpha]s=Sort[SchmidtCoefficients[\[Psi],sys,dim]//Chop,Greater],
\[Beta]s=Sort[SchmidtCoefficients[\[Phi],sys,dim]//Chop,Greater]
},

Min[Total[(\[Alpha]s^2)[[#;;]]]/Total[(\[Beta]s^2)[[#;;]]]&/@Range[Length[Cases[\[Beta]s,Except[0]]]]]
]

Negativity[\[Rho]_,dims_List,part_List] := (TraceNorm[PartialTranspose[\[Rho],dims,part]]-1)(*/2*);
Negativity[\[Rho]_,part_List] := (TraceNorm[PartialTranspose[\[Rho],part]]-1)(*/2*);

PureQ[\[Rho]_?MatrixQ] := FullSimplify[\[Rho]==MatrixPower[\[Rho],2]];

SchmidtCoefficients[\[Psi]_,{da_,db_}]:=Diagonal[SingularValueDecomposition[Partition[\[Psi],db]][[2]]]
SchmidtCoefficients[\[Psi]_,sys_,dim_]:=Sqrt[Eigenvalues[PartialTrace[KetBra[\[Psi]],sys,dim]]]

End[];


(* ::Section::Closed:: *)
(*Fidelity*)


FidelityQubits::usage = "FidelityQubits[A,B] returns the fidelity of two mixed qubit states A and B.";
SingletFidelity::usage = "SingletFidelity[\[Rho]] returns \[LeftAngleBracket]\!\(\*SuperscriptBox[\(\[CapitalPhi]\), \(+\)]\)|\[Rho]|\!\(\*SuperscriptBox[\(\[CapitalPhi]\), \(+\)]\)\[RightAngleBracket].
SingletFidelity[\[Rho],i] returns \[LeftAngleBracket]\!\(\*SubscriptBox[\(\[CapitalPhi]\), \(i\)]\)|\[Rho]|\!\(\*SubscriptBox[\(\[CapitalPhi]\), \(i\)]\)\[RightAngleBracket], with \!\(\*SubscriptBox[\(\[CapitalPhi]\), \(0\)]\)=\!\(\*SuperscriptBox[\(\[CapitalPhi]\), \(+\)]\), \!\(\*SubscriptBox[\(\[CapitalPhi]\), \(1\)]\)=\!\(\*SuperscriptBox[\(\[CapitalPhi]\), \(-\)]\), \!\(\*SubscriptBox[\(\[CapitalPhi]\), \(2\)]\)=\!\(\*SuperscriptBox[\(\[CapitalPsi]\), \(+\)]\), \!\(\*SubscriptBox[\(\[CapitalPhi]\), \(3\)]\)=\!\(\*SuperscriptBox[\(\[CapitalPsi]\), \(-\)]\).";

Begin["`Private`"];

FidelityQubits[A_?MatrixQ,B_?MatrixQ] := Tr[A.B]+2Sqrt[Det[A]Det[B]];

SingletFidelity[\[Rho]_?MatrixQ,i_Integer:0]:=BraKet[BellState[i],\[Rho],BellState[i]]

End[];


(* ::Section::Closed:: *)
(*Notation*)


CirclePlus::usage = "CirclePlus";
CirclePlusExp::usage = "CirclePlusExp[b_,e_] returns \!\(\*SuperscriptBox[\"b\", 
RowBox[{\"\[CirclePlus]\", \"e\"}]]\).";
CircleTimes::usage = "CircleTimes";
TensorExp::usage = "TensorExp[b_,e_] returns \!\(\*SuperscriptBox[\"b\", 
RowBox[{\"\[CircleTimes]\", \"e\"}]]\).";

Begin["`Private`"];

CirclePlus[a__?VectorQ] := Join[a]
CirclePlus[a_?MatrixQ,b_?MatrixQ] := ArrayFlatten[
	{
		{a,ConstantArray[0,{Dimensions[a][[1]],Dimensions[b][[2]]}]}
		,
		{ConstantArray[0,{Dimensions[b][[1]],Dimensions[a][[2]]}],b}
	}
];
CirclePlus[a_,b_,c__] := CirclePlus[CirclePlus[a,b],c];

CirclePlusExp[b_,e_Integer] := CirclePlus@@ConstantArray[b,e];

CircleTimes[a_?MatrixQ,b_?MatrixQ] := ArrayFlatten[Outer[Times,a,b]];
CircleTimes[a_?VectorQ,b_?VectorQ] := Flatten[Outer[Times,a,b]];
CircleTimes[a_,b_,c__] := CircleTimes[CircleTimes[a,b],c];
CircleTimes[a_] := a

TensorExp[b_,0] := 1;
TensorExp[b_,1] := b;
TensorExp[b_,e_Integer] := CircleTimes@@ConstantArray[b,e];
TensorExp/:MakeBoxes[TensorExp[a_,n_],form_]:=SuperscriptBox[MakeBoxes[a,form],RowBox[{"\[CircleTimes]",MakeBoxes[n,form]}]];
MakeExpression[SuperscriptBox[a_,RowBox[{"\[CircleTimes]",n_}]],form_]:=MakeExpression[RowBox[{"TensorExp","[",a,",",n,"]"}],form];

End[];


(* ::Section::Closed:: *)
(*Partial trace*)


PartialTrace::usage="PartialTrace[RHO,SYS ,DIMs] traces out system SYS of a matrix RHO with subsystem dimensions specified by DIMS.
 If no dimensions are specified PartialTrace[RHO,SYS]  assumes a 2x2 system.
 If only one is specified, PartialTrace[RHO,SYS,dim1], it assumes a dim1 x dim1 system. DIM={dim1,dim2,dim3} specifies a dim1 x dim2 x dim3 system.
PartialTrace[RHO,SYS ,DIMS] with SYS={SYS1,SYS2,..} performs the partial trace over systems {SYS1,SYS2,..}.
";
ReducedQubitState::usage = "ReducedQubitState[\[Psi],i] returns the reduced qubit state of subsystem i.";
ReducedQubitState::usage = "ReducedQubitState[\[Rho],i] returns the reduced qubit state of subsystem i.";
ReducedQubitStates::usage = "ReducedQubitStates[\[Psi]] returns a list of all the reduced qubit states.";
ReducedQubitStates::usage = "ReducedQubitStates[\[Rho]] returns a list of all the reduced qubit states.";

Begin["`Private`"];

(* From QItoolbox *)
(*Adapted from Tony Cubitt's matlab function*)
PartialTrace[A_,sysi_?IntegerQ,dims_]/;Length[A]==Times@@dims:=Module[{dim1,dim2,dim3,indx,sys},sys=sysi;Switch[Length[dims],0,{dim1,dim2,dim3}={2,1,2};If[sysi==2,sys=3],1,{dim1,dim2,dim3}={dims[[1]],1,dims[[1]]};If[sysi==2,sys=3],2,{dim1,dim2,dim3}={dims[[1]],1,dims[[2]]};If[sysi==2,sys=3],3,{dim1,dim2,dim3}=dims,_?(#>3&),({dim1,dim2,dim3}={Times@@dims[[1;;sys-1]],dims[[sys]],Times@@dims[[sys+1;;]]});sys=2;];Switch[sys,1,indx=Range[1,dim2*dim3];Sum[A[[indx+k*dim2*dim3,indx+k*dim2*dim3]],{k,0,dim1-1}],2,indx=Array[1&,dim1]\[CircleTimes]Range[1,dim3]+dim2 dim3 *Range[0,dim1-1]\[CircleTimes] Array[1&,dim3];Sum[A[[indx+k*dim3,indx+k*dim3]],{k,0,dim2-1}],3,indx=dim3*Range[0,dim1*dim2-1];Sum[A[[indx+k,indx+k]],{k,1,dim3}]]] 
PartialTrace[A_,sys_?IntegerQ]/;Length[A]==4:=PartialTrace[A,sys,{2,2}];
PartialTrace[A_,sys_?IntegerQ,dim_?IntegerQ]/;Length[A]==dim^2:=PartialTrace[A,sys,{dim,dim}]
PartialTrace[A_,sys_List,dims_]:=Module[{Atemp,dimt,syst},Atemp=A;dimt=dims;syst=Sort[sys,Greater];Do[Atemp=PartialTrace[Atemp,syst[[i]],dimt];dimt=Drop[dimt,{syst[[i]]}],{i,Length[sys]}];Atemp]

ReducedQubitState[\[Psi]_?VectorQ,i_]:=ReducedQubitState[KetBra[\[Psi]],i]
ReducedQubitState[\[Rho]_?MatrixQ,i_]:=Module[{n,m},
	{n,m}=Log[2,Dimensions[\[Rho]]];
	If[n!=m,Abort[]];
	If[!(n\[Element]Integers)||n<1,Abort[]];
	PartialTrace[\[Rho],DeleteCases[Range[n],i],ConstantArray[2,n]]
]

ReducedQubitStates[\[Psi]_?(VectorQ[#]&&Log[2,Length[#]]>0&&Log[2,Length[#]]\[Element]Integers&)]:=ReducedQubitState[KetBra[\[Psi]],#]&/@Range[Log[2,Length[\[Psi]]]]
ReducedQubitStates[\[Rho]_?(MatrixQ[#]&&(Equal@@Dimensions[#])&&Log[2,Dimensions[#][[1]]]>0&&Log[2,Dimensions[#][[1]]]\[Element]Integers&)]:=ReducedQubitState[\[Rho],#]&/@Range[Log[2,Dimensions[\[Rho]][[1]]]]

End[];


(* ::Section::Closed:: *)
(*Partial transposition*)


PartialTranspose::usage="PartialTranspose[\[Rho]_,dims_,part_]: given a multipartite state \[Rho] [of dims dims={d1,d2,d3,..}]  written in the computational basis returns the matrix after performing partial transpositions on subsystems part={n1,n2,...}. If dims is not given: trans[rho_,part_]: qubits subsystems is assumed ";
Unflatten::usage="Unflatten[list,dims]: takes vector list and reshapes it into a tensor by sequentially partitioning the list in \!\(\*SubscriptBox[\"dim\", \"n\"]\), then \!\(\*SubscriptBox[\"dim\", 
RowBox[{\"n\", \"-\", \"1\"}]]\)..., dim={\!\(\*SubscriptBox[\"dim\", \"1\"]\),\!\(\*SubscriptBox[\"dim\", \"2\"]\),..\!\(\*SubscriptBox[\"dim\", \"n\"]\)}. The list must have \!\(\*SubscriptBox[\"\[CapitalPi]\", \"i\"]\)\!\(\*SubscriptBox[\"d\", \"i\"]\) elements. Analagous to reshape function in matlab.";

Begin["`Private`"];

(* From QItoolbox *)
PartialTranspose[\[Rho]_,dims_List,part_List] := Module[
	{s,eo,n},

	n=Length[dims];
	eo=Range[1,2*n];
	({eo[[#]],eo[[#+n]]}={eo[[#+n]],eo[[#]]})&/@ part;
	Partition[Flatten[Transpose[Unflatten[Flatten[\[Rho]],Join[dims,dims]],eo]],Times@@dims]
];
PartialTranspose[\[Rho]_,part_List] := Module[
	{s,eo,dims,n},

	n=Log[2,Length[\[Rho]]];
	eo=Range[1,2*n];
	dims=Array[2&,n];
	({eo[[#]],eo[[#+n]]}={eo[[#+n]],eo[[#]]})&/@ part;
	Partition[Flatten[Transpose[Unflatten[Flatten[\[Rho]],Join[dims,dims]],eo]],Times@@dims]]

(* From QItoolbox *)
Unflatten[e_,{d__?((IntegerQ[#]&&Positive[#])&)}] := Fold[Partition,e,Take[{d},{-1,2,-1}]] /;(Length[e]===Times[d])

End[];


(* ::Section:: *)
(*SLOCC classes*)


(* ::Subsection::Closed:: *)
(*4-qubits*)


SLOCCFamilyGabcd::usage = "SLOCCFamilyGabcd[a,b,c,d] gives the \!\(\*SubscriptBox[\(G\), \(abcd\)]\) family of 4-qubit SLOCC classes.";
SLOCCFamilyLabc2::usage = "SLOCCFamilyLabc2[a,b,c] gives the \!\(\*SubscriptBox[\(L\), SubscriptBox[\(abc\), \(2\)]]\) family of 4-qubit SLOCC classes.";
SLOCCFamilyLa2b2::usage = "SLOCCFamilyLa2b2[a,b] gives the \!\(\*SubscriptBox[\(L\), \(\*SubscriptBox[\(a\), \(2\)] \*SubscriptBox[\(b\), \(2\)]\)]\) family of 4-qubit SLOCC classes.";
SLOCCFamilyLab3::usage = "SLOCCFamilyLab3[a,b] gives the \!\(\*SubscriptBox[\(L\), SubscriptBox[\(ab\), \(3\)]]\) family of 4-qubit SLOCC classes.";

SLOCCFamilyLa4::usage = "SLOCCFamilyLa4[a] gives the \!\(\*SubscriptBox[\(L\), SubscriptBox[\(a\), \(4\)]]\) family of 4-qubit SLOCC classes.";
SLOCCFamilyLa2o31::usage ="SLOCCFamilyLa2o31[a] gives the \!\(\*SubscriptBox[\(L\), \(\*SubscriptBox[\(a\), \(2\)] \*SubscriptBox[\(0\), \(3\[CirclePlus]1\)]\)]\) family of 4-qubit SLOCC classes.";

SLOCCFamilyLo53::usage = "SLOCCFamilyLo53 gives the \!\(\*SubscriptBox[\(L\), SubscriptBox[\(0\), \(5\[CirclePlus]3\)]]\) family of 4-qubit SLOCC classes.";
SLOCCFamilyLo71::usage = "SLOCCFamilyLo71 gives the \!\(\*SubscriptBox[\(L\), SubscriptBox[\(0\), \(7\[CirclePlus]1\)]]\) family of 4-qubit SLOCC classes.";
SLOCCFamilyLo31o31::usage = "SLOCCFamilyLo31o31 gives the \!\(\*SubscriptBox[\(L\), \(\*SubscriptBox[\(0\), \(3\[CirclePlus]1\)] \*SubscriptBox[\(0\), \(3\[CirclePlus]1\)]\)]\) family of 4-qubit SLOCC classes.";

Begin["`Private`"];

SLOCCFamilyGabcd[a_,b_,c_,d_]:=(a+d)/2 (ComputationalKet[{0,0,0,0}]+ComputationalKet[{1,1,1,1}])+(a-d)/2 (ComputationalKet[{0,0,1,1}]+ComputationalKet[{1,1,0,0}])+(b+c)/2 (ComputationalKet[{0,1,0,1}]+ComputationalKet[{1,0,1,0}])+(b-c)/2 (ComputationalKet[{0,1,1,0}]+ComputationalKet[{1,0,0,1}])
SLOCCFamilyLabc2[a_,b_,c_]:=(a+b)/2 (ComputationalKet[{0,0,0,0}]+ComputationalKet[{1,1,1,1}])+(a-b)/2 (ComputationalKet[{0,0,1,1}]+ComputationalKet[{1,1,0,0}])+c(ComputationalKet[{0,1,0,1}]+ComputationalKet[{1,0,1,0}])+ComputationalKet[{0,1,1,0}]
SLOCCFamilyLa2b2[a_,b_]:=a(ComputationalKet[{0,0,0,0}]+ComputationalKet[{1,1,1,1}])+b(ComputationalKet[{0,1,0,1}]+ComputationalKet[{1,0,1,0}])+ComputationalKet[{0,1,1,0}]+ComputationalKet[{0,0,1,1}]
SLOCCFamilyLab3[a_,b_]:=a(ComputationalKet[{0,0,0,0}]+ComputationalKet[{1,1,1,1}])+(a+b)/2 (ComputationalKet[{0,1,0,1}]+ComputationalKet[{1,0,1,0}])+(a-b)/2 (ComputationalKet[{0,1,1,0}]+ComputationalKet[{1,0,0,1}])+I/Sqrt[2] (ComputationalKet[{0,0,0,1}]+ComputationalKet[{0,0,1,0}]+ComputationalKet[{0,1,1,1}]+ComputationalKet[{1,0,1,1}])

SLOCCFamilyLa4[a_]:=a(ComputationalKet[{0,0,0,0}]+ComputationalKet[{0,1,0,1}]+ComputationalKet[{1,0,1,0}]+ComputationalKet[{1,1,1,1}])+I ComputationalKet[{0,0,0,1}]+ComputationalKet[{0,1,1,0}]-I ComputationalKet[{1,0,1,1}]
SLOCCFamilyLa2o31[a_]:=a(ComputationalKet[{0,0,0,0}]+ComputationalKet[{1,1,1,1}])+(ComputationalKet[{0,0,1,1}]+ComputationalKet[{0,1,0,1}]+ComputationalKet[{0,1,1,0}])

SLOCCFamilyLo53=ComputationalKet[{0,0,0,0}]+ComputationalKet[{0,1,0,1}]+ComputationalKet[{1,0,0,0}]+ComputationalKet[{1,1,1,0}];
SLOCCFamilyLo71=ComputationalKet[{0,0,0,0}]+ComputationalKet[{1,0,1,1}]+ComputationalKet[{1,1,0,1}]+ComputationalKet[{1,1,1,0}];
SLOCCFamilyLo31o31=ComputationalKet[{0,0,0,0}]+ComputationalKet[{0,1,1,1}];

End[];


(* ::Section:: *)
(*States and operators*)


(* ::Subsection::Closed:: *)
(*Bell, magic, GHZ states, W states*)


BellState::usage = "BellState[k] returns the Bell state in the ZZ (computational) basis (k=0,1,2,3).
BellState[k,{\"A\",\"B\"}] returns the Bell state in the AB basis (A,B = X,Y,Z).
BellState[a,b].
BellState[a,b,{\"A\",\"B\"}].";

GHZState::usage = "GHZState[]
GHZState[n]";

MagicState::usage = "MagicState[k]
MagicState[k,{\"A\",\"B\"}]";

SymmetricState::usage = "SymmetricState[n,k] returns the symmetric state of n qubits, with n-k |0\[RightAngleBracket] and k |1\[RightAngleBracket].";

WState::usage = "WState[]
WState[n]";

Begin["`Private`"];

BellState[k_Integer,basis_List:{"Z","Z"}] := Module[
	{
	uA = UpState[basis[[1]]],
	dA = DownState[basis[[1]]],
	uB = UpState[basis[[2]]],
	dB = DownState[basis[[2]]]
	},

	Switch[k,
		0, 1/Sqrt[2] (uA\[CircleTimes]uB+dA\[CircleTimes]dB)
		,
		1, 1/Sqrt[2] (uA\[CircleTimes]uB-dA\[CircleTimes]dB)
		,
		2, 1/Sqrt[2] (uA\[CircleTimes]dB+dA\[CircleTimes]uB)
		,
		3, 1/Sqrt[2] (uA\[CircleTimes]dB-dA\[CircleTimes]uB)
	]
];
BellState[a_Integer,b_Integer,basis_List:{"Z","Z"}]:=If[a==0,
	If[b==0,BellState[0,basis],BellState[1,basis]],
	If[b==0,BellState[2,basis],BellState[3,basis]]
]/;0<=a<=1&&0<=b<=1;
BellState/:MakeBoxes[BellState[a_,b_],form_]:=SubscriptBox["\[CapitalPhi]",RowBox[{MakeBoxes[a,form],",",MakeBoxes[b,form]}]];
MakeExpression[SubscriptBox["\[CapitalPhi]",RowBox[{a_,",",b_}]],form_]:=MakeExpression[RowBox[{"BellState","[",a,",",b,"]"}],form];

GHZState[] := GHZState[3];
GHZState[n_Integer/;n>=2] := 1/Sqrt[2] (TensorExp[UpState[],n]+TensorExp[DownState[],n]);

MagicState[k_Integer,basis_List:{"Z","Z"}] := Module[
	{
	uA = UpState[basis[[1]]],
	dA = DownState[basis[[1]]],
	uB = UpState[basis[[2]]],
	dB = DownState[basis[[2]]]
	},

	Switch[k,
		0, 1/Sqrt[2] (uA\[CircleTimes]uB+dA\[CircleTimes]dB)
		,
		1, I/Sqrt[2] (uA\[CircleTimes]uB-dA\[CircleTimes]dB)
		,
		2, I/Sqrt[2] (uA\[CircleTimes]dB+dA\[CircleTimes]uB)
		,
		3, 1/Sqrt[2] (uA\[CircleTimes]dB-dA\[CircleTimes]uB)
	]
];

SymmetricState[n_,k_]:=1/Sqrt[Binomial[n,k]] Total[ComputationalKet/@Permutations[Join[ConstantArray[0,n-k],ConstantArray[1,k]]]]

WState[]:=WState[3];
WState[n_Integer?(#>=2&)]:=SymmetricState[n,1]

End[];


(* ::Subsection::Closed:: *)
(*BellDiagonal, Identity, Werner*)


BellDiagonal::usage = "BellDiagonal[{a,b,c,d}] returns  a|\!\(\*SuperscriptBox[\(\[CapitalPhi]\), \(+\)]\)\[RightAngleBracket]\[LeftAngleBracket]\!\(\*SuperscriptBox[\(\[CapitalPhi]\), \(+\)]\)|+b|\!\(\*SuperscriptBox[\(\[CapitalPhi]\), \(-\)]\)\[RightAngleBracket]\[LeftAngleBracket]\!\(\*SuperscriptBox[\(\[CapitalPhi]\), \(-\)]\)|+c|\!\(\*SuperscriptBox[\(\[CapitalPsi]\), \(+\)]\)\[RightAngleBracket]\[LeftAngleBracket]\!\(\*SuperscriptBox[\(\[CapitalPsi]\), \(+\)]\)|+d|\!\(\*SuperscriptBox[\(\[CapitalPsi]\), \(-\)]\)\[RightAngleBracket]\[LeftAngleBracket]\!\(\*SuperscriptBox[\(\[CapitalPsi]\), \(-\)]\)|."
BellDiagonalCoefficients::usage = "BellDiagonalCoefficients[\[Rho]] returns {\[LeftAngleBracket]\!\(\*SubscriptBox[\(\[CapitalPhi]\), \(i\)]\)|\[Rho]|\!\(\*SubscriptBox[\(\[CapitalPhi]\), \(i\)]\)\[RightAngleBracket]\!\(\*SubscriptBox[\(}\), \(i = 0, 1, 2, 3\)]\), with \!\(\*SubscriptBox[\(\[CapitalPhi]\), \(0\)]\)=\!\(\*SuperscriptBox[\(\[CapitalPhi]\), \(+\)]\), \!\(\*SubscriptBox[\(\[CapitalPhi]\), \(1\)]\)=\!\(\*SuperscriptBox[\(\[CapitalPhi]\), \(-\)]\), \!\(\*SubscriptBox[\(\[CapitalPhi]\), \(2\)]\)=\!\(\*SuperscriptBox[\(\[CapitalPsi]\), \(+\)]\), \!\(\*SubscriptBox[\(\[CapitalPhi]\), \(3\)]\)=\!\(\*SuperscriptBox[\(\[CapitalPsi]\), \(-\)]\)."

Id::usage = "\!\(\*SubscriptBox[\"Id\", \"n\"]\) returns the n-dimensional identity matrix."
WernerState::usage = "WernerState[x] returns x |\!\(\*SubscriptBox[\"\[CapitalPhi]\", 
RowBox[{\"0\", \",\", \"0\"}]]\)\[RightAngleBracket]\[LeftAngleBracket]\!\(\*SubscriptBox[\"\[CapitalPhi]\", 
RowBox[{\"0\", \",\", \"0\"}]]\)| + (1-x)\!\(\*FractionBox[\"Id\", \"4\"]\)."

Begin["`Private`"];

BellDiagonal[{a_,b_,c_,d_}]:=a KetBra[Subscript[\[CapitalPhi], 0,0]]+b KetBra[Subscript[\[CapitalPhi], 0,1]]+c KetBra[Subscript[\[CapitalPhi], 1,0]]+d KetBra[Subscript[\[CapitalPhi], 1,1]]
BellDiagonalCoefficients[\[Rho]_?MatrixQ]:=BraKet[BellState[#],\[Rho],BellState[#]]&/@Range[0,3]

Subscript[Id, n_]:=IdentityMatrix[n]

WernerState[x_]:=x KetBra[BellState[0]]+(1-x) Subscript[Id, 4]/4

End[];


(* ::Subsection::Closed:: *)
(*Qubits*)


BlochQubit::usage = "BlochQubit[{a,b,c}] returns single qubit density matrix specified by bloch vector r={a,b,c}.
By default, r is interpreted in Cartesian coordinates, but coordinate system can be choosen with option Coordinates->\"Cartesian\" or Coordinates->\"Spherical\".";
DownState::usage = "DownState[basis], where basis is either \"X\", \"Y\" or \"Z\".";
UpState::usage = "UpState[basis], where basis is either \"X\", \"Y\" or \"Z\".";
ComputationalKet::usage = "ComputationalKet[bitstring] returns |bitstring\[RightAngleBracket].
ComputationalKet[n,list] returns the computational ket of n qubits, with qubits in list in the state |1\[RightAngleBracket] and the rest in |0\[RightAngleBracket].";
ComputationalKetQ::usage = "ComputationalKetQ[vector] returns True if vector is a valid state of the computational basis.";
ComputationalKetToBinaryVector::usage ="ComputationalKetToBinaryVector[vector] returns the bitstring corresponding to vector=|bitstring\[RightAngleBracket].";
ComputationalSupport::usage = "ComputationalSupport[\[Psi]] returns the list of x (an element of the computational basis) such that \[LeftAngleBracket]x|\[Psi]\[RightAngleBracket] is different from 0.";
ComputationalExpansion::usage = "ComputationalExpansion[\[Psi]] returns {{a1,a2,...},{x1,x2,...}} such that |\[Psi]\[RightAngleBracket]=a1|x1\[RightAngleBracket]+a2|x2\[RightAngleBracket]+...";
\[Psi]example::usage = "\[Psi]example[n] gives the vector {\!\(\*SubscriptBox[\(a\), \(1\)]\),\!\(\*SubscriptBox[\(a\), \(2\)]\),...,\!\(\*SubscriptBox[\(a\), SuperscriptBox[\(2\), \(n\)]]\)}.";

Begin["`Private`"];

Options[BlochQubit]={Coordinates->"Cartesian"};
BlochQubit[r_List,OptionsPattern[]] := Module[
	{},
	Switch[OptionValue[Coordinates],
	"Cartesian",
		1/2 (Plus@@(Prepend[r,1]PauliVector[]))
	,
	"Spherical",
		1/2 (Plus@@({1,r[[1]]Sin[r[[2]]]Cos[r[[3]]],r[[1]]Sin[r[[2]]]Sin[r[[3]]],r[[1]]Cos[r[[2]]]}PauliVector[]))
	]
];

DownState[basis_String:"Z"] := Switch[basis,"X",1/Sqrt[2] {1,-1},"Y",1/Sqrt[2] {1,-I},"Z",{0,1}]
UpState[basis_String:"Z"] := Switch[basis,"X",1/Sqrt[2] {1,1},"Y",1/Sqrt[2] {1,I},"Z",{1,0}]

ComputationalKet[bitstring_List] := OperatorAt[PauliMatrix[1],bitstring,Length[bitstring],AtList->"Binary"].(TensorExp[{1,0},Length[bitstring]])
ComputationalKet[n_,positions_]:=OperatorAt[PauliMatrix[1],positions,n,AtList->"Positions"].(TensorExp[{1,0},n])

ComputationalKetQ[ket_]:=VectorQ[ket]&&Log[2,Length[ket]]\[Element]Integers&&MemberQ[ComputationalKet/@Tuples[{0,1},Log[2,Length[ket]]],ket]
ComputationalKetToBinaryVector[ket_?ComputationalKetQ]:=BraKet[ket,Tuples[{0,1},Log[2,Length[ket]]]]
ComputationalSupport[\[Psi]_?VectorQ]:=Module[{n=Log[2,Length[\[Psi]]]},
Select[Tuples[{0,1},n],BraKet[ComputationalKet[#],\[Psi]]!=0&]]

ComputationalExpansion[\[Psi]_?VectorQ]:={Select[\[Psi],#!=0&],ComputationalSupport[\[Psi]]}

\[Psi]example[n_]:=Symbol["a"<>ToString[#]]&/@Range[2^n]

End[];


(* ::Subsection::Closed:: *)
(*1-qubit operators*)


HadamardGate::usage = "HadamardGate[]";
PauliProjector::usage = "PauliProjector[i,s] is the projector onto the eigenvector of the i Pauli matrix with eigenvalue s (+1 or -1)";
PauliVector::usage = "PauliVector[] returns the vector of the four Pauli Matrices {\!\(\*SubscriptBox[\"\[Sigma]\", \"0\"]\),\!\(\*SubscriptBox[\"\[Sigma]\", \"1\"]\),\!\(\*SubscriptBox[\"\[Sigma]\", \"2\"]\),\!\(\*SubscriptBox[\"\[Sigma]\", \"3\"]\)}";
PhaseGate::usage = "PhaseGate[] returns the singlet qubit phase gate.
PhaseGate[\[Alpha]] returns diag(1,\!\(\*SuperscriptBox[\(e\), \(i\[Alpha]\)]\))."

Begin["`Private`"];

HadamardGate[] := HadamardMatrix[2];
Unprotect[PauliMatrix];
PauliMatrix[i_Integer] := PauliMatrix[i]/;0<=i<=3;
PauliMatrix/:MakeBoxes[PauliMatrix[i_],form_] := SuperscriptBox["\[Sigma]",RowBox[{"(",MakeBoxes[i,form],")"}]];
MakeExpression[SuperscriptBox["\[Sigma]",RowBox[{"(",i_,")"}]],form_] := MakeExpression[RowBox[{"PauliMatrix","[",i,"]"}],form];
Protect[PauliMatrix];

PauliProjector[i_Integer,s_Integer] := Module[{},
	If[s!=-1&&s!=1,Null,
		(IdentityMatrix[2]+s PauliMatrix[i])/2
	]
]

PauliVector[] := PauliMatrix[Range[0,3]];
PauliVector[i_Integer] := PauliMatrix[i];

PhaseGate[] := {{1,0},{0,I}};
PhaseGate[\[Alpha]_] := {{1,0},{0,Exp[I \[Alpha]]}};

End[];


(* ::Subsection::Closed:: *)
(*2-qubits operators*)


ControlledGate::usage = "ControlledGate[gate]";
ControlledNot::usage = "ControlledNot[]";
ControlledPhase::usage = "ControlledPhase[] gives the 2-qubits controlled phase gate.
ControlledPhase[n,a,b] gives the controlled phase applied to a system of n qubits, with control qubit a and target qubit b.";
GeneralizedControlledPhase::usage = "GeneralizedControlledPhase[n] gives the n-qubits controlled phase gate.
GeneralizedControlledPhase[n,i] applies a \!\(\*SubscriptBox[\(CPHASE\), \({i1, i2,  ... , ik}\)]\) to a system of n qubits.
GeneralizedControlledPhase[n,i,\[Alpha]] applies a Id-(1-\!\(\*SuperscriptBox[\(\[ExponentialE]\), \(\[ImaginaryI]\[Alpha]\)]\)|11...1\[RightAngleBracket]\[LeftAngleBracket]11...1|) gate.";
SwapGate::usage = "SwapGate[]";

Begin["`Private`"];

ControlledGate[gate_] := IdentityMatrix[2]\[CirclePlus]gate;

ControlledNot[] := {{1,0,0,0},{0,1,0,0},{0,0,0,1},{0,0,1,0}};

ControlledPhase[] := {{1,0,0,0},{0,1,0,0},{0,0,1,0},{0,0,0,-1}};
ControlledPhase[n_,a_,b_] := OperatorsAt[{PauliProjector[3,+1],IdentityMatrix[2]},{a,b},n]+OperatorsAt[{PauliProjector[3,-1],PauliMatrix[3]},{a,b},n];

GeneralizedControlledPhase[n_] := IdentityMatrix[2^n]-2KetBra[



\!\(\*SuperscriptBox[\({0, 1}\), \(\[CircleTimes]n\)]\)]
GeneralizedControlledPhase[n_,i_List]:=OperatorAt[Id,i,n]-2OperatorAt[PauliProjector[3,-1],i,n]
GeneralizedControlledPhase[n_,i_List,\[Alpha]_]:=OperatorAt[Id,i,n]-(1-E^(I \[Alpha]))OperatorAt[PauliProjector[3,-1],i,n]

SwapGate[] := {{1,0,0,0},{0,0,1,0},{0,1,0,0},{0,0,0,1}};

End[];


(* ::Subsection::Closed:: *)
(*Operator at*)


OperatorAt::usage = "OperatorAt[operator,i,totalLength] returns operator A applied at position i (if it is an integer) or at positions in i (if it is a list of integers), and the identity at the rest of positions.";
OperatorsAt::usage = "OperatorsAt[operatorList,AtList,totalLength]";

AtList::usage = "Option for OperatorAt, indicating if the list indicates Positions or is a Binary vector.";

Begin["`Private`"];

Options[OperatorAt] = {AtList->"Positions"};
OperatorAt[A_?MatrixQ,atList_List,n_Integer,OptionsPattern[]] := Module[
	{d,atListPos},

	atListPos = If[OptionValue[AtList]=="Binary",
		If[Length[atList]!=n,Abort[]];
		Flatten[Position[atList,1]]
		,
		atList
	];

	If[Dimensions[A][[1]]==Dimensions[A][[2]],d=Dimensions[A][[1]],Abort[]];

	CircleTimes@@ReplacePart[
		ConstantArray[IdentityMatrix[d],n],
		#->A & /@ atListPos
	]
];
OperatorAt[A_?MatrixQ,i_Integer,n_Integer] := Module[
	{
	d
	},

	If[Dimensions[A][[1]]==Dimensions[A][[2]],d=Dimensions[A][[1]],Abort[]];

	Switch[i,
	1,
		A\[CircleTimes]TensorExp[IdentityMatrix[d],n-i]
	,
	n,
		TensorExp[IdentityMatrix[d],i-1]\[CircleTimes]A
	,
	_,
		TensorExp[IdentityMatrix[d],i-1]\[CircleTimes]A\[CircleTimes]TensorExp[IdentityMatrix[d],n-i]
	]
]
OperatorAt[A_?MatrixQ,1,1] := A
OperatorAt[A_?MatrixQ,{0},1,AtList->"Binary"] := IdentityMatrix[Dimensions[A][[1]]]
OperatorAt[A_?MatrixQ,{1},1,AtList->"Binary"] := A
OperatorAt/:MakeBoxes[OperatorAt[A_,i_,n_],form_]:=SubsuperscriptBox[MakeBoxes[A,form],MakeBoxes[i,form],MakeBoxes[n,form]];
MakeExpression[SubsuperscriptBox[A_,i_,n_],form_]:=MakeExpression[RowBox[{"OperatorAt","[",A,",",i,",",n,"]"}],form];

OperatorsAt[opList_List,atList_List,n_Integer]:=Module[
	{
	d=2
	},

	If[Length[opList]!=Length[atList],Abort[]];
	If[Length[#]>1,Abort[]]&/@Gather[atList];

	CircleTimes @@ ReplacePart[
		ConstantArray[IdentityMatrix[d],n],
		#[[1]]->#[[2]]&/@Transpose[{atList,opList}]
	]
]

End[];


(* ::Subsection::Closed:: *)
(*Expected value*)


Expected::usage = "Expected[op,i,\[Rho]] returns the expected vaule of the operator applied to subsystem i of a state \[Rho].";

Begin["`Private`"];

Expected[op_,i_,\[Psi]_?VectorQ]:=Expected[op,i,KetBra[\[Psi]]]
Expected[op_,i_,\[Rho]_?MatrixQ]:=Tr[OperatorAt[op,i,Log[2,Dimensions[\[Rho]][[1]]]].\[Rho]]

End[];


(* ::Section::Closed:: *)
(*Shorthands*)


QuantumInformationShorthands::usage = "QuantumInformationShorthands[] includes the QuantumInformation`Shorthands` context";

Begin["`Private`"];

QuantumInformationShorthands[]:=($ContextPath=DeleteDuplicates[Prepend[$ContextPath,"QuantumInformation`Shorthands`"]]);

End[];


(* ::Subsection::Closed:: *)
(*Constants*)


Begin["`Shorthands`"];

CNOT = ControlledNot[];

H = HadamardMatrix[2];

Id = IdentityMatrix[2];

\[Sigma]x = PauliMatrix[1];
\[Sigma]y = PauliMatrix[2];
\[Sigma]z = PauliMatrix[3];
\[Sigma] = PauliVector[];

X = PauliMatrix[1];
Y = PauliMatrix[2];
Z = PauliMatrix[3];

End[];


(* ::Subsection::Closed:: *)
(*Functions*)


Begin["`Shorthands`"];

(*\[ScriptCapitalA]::usage = "Subsuperscript[\[ScriptCapitalA], indices, {n,c}][\[Psi]] is a shorthand for SLOCCGeneralPolynomialInvariant[n,c,indices,\[Psi]].";*)
(*\[ScriptCapitalB]::usage = "Subsuperscript[\[ScriptCapitalB], indices, (n)][\[Psi]] is a shorthand for SLOCCPolynomialInvariantB[n,indices,\[Psi]].";*)
\!\(
\(\*SubsuperscriptBox[\(\[ScriptCapitalA]\), \(indices_List\), \({n_, c_}\)]\)[\[Psi]_]\):=SLOCCGeneralPolynomialInvariant[n,c,indices,\[Psi]]
\!\(
\(\*SubsuperscriptBox[\(\[ScriptCapitalB]\), \(indices_List\), \((n_)\)]\)[\[Psi]_]\):=SLOCCPolynomialInvariantB[n,indices,\[Psi]]

CK::usage = "CK[x] and CK[n,x] are shorthands for ComputationalKet[x] and ComputationalKet[n,x]";
CS::usage = "CS[x] is a shorthand for ComputationalSupport[x]";

Ket::usage = "\!\(\*TemplateBox[{RowBox[{\"x1\", \",\", \"x2\", \",\", \"...\"}]},\n\"Ket\"]\) and \!\(\*TemplateBox[{RowBox[{\"{\", RowBox[{\"x1\", \",\", \"x2\", \",\", \"...\"}], \"}\"}]},\n\"Ket\"]\) are shorthands for ComputationalKet[{x1,x2,...}]. The usage of this notation is still under development.";

End[];


Begin["`Shorthands`Private`"];

CK[x_List]:=ComputationalKet[x]
CK[n_,x_]:=ComputationalKet[n,x]
CS[x_]:=ComputationalSupport[x]

Ket[x_List]:=ComputationalKet[x]
Ket[x__]:=ComputationalKet[{x}]

End[];


(* ::Section::Closed:: *)
(*EndPackage*)


EndPackage[];

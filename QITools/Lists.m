(* ::Package:: *)

(* ::Title:: *)
(*QITools package: Lists*)


(* ::Text:: *)
(*A package with list tools for Mathematica *)
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


BeginPackage["QITools`Lists`"];


(* ::Section::Closed:: *)
(*Data operations*)


MeanData::usage = "PlusData[{data1,data2,...}] averages data wisely.";
PlusData::usage = "PlusData[{data1,data2,...}] sums data wisely.";

Begin["`Private`"];

MeanData[dataList_List]:=Module[
	{x,y,data},
	x=DeleteDuplicates[Flatten[Part[#,All,1]&/@dataList]];
	data=Flatten[dataList,1];
	Table[
		y=Select[data,#[[1]]==i&][[All,2]];
		{i,Plus@@y/Length[y]}
		,{i,x}
	]
]

PlusData[dataList_List]:=Module[
	{x,data},
	x=DeleteDuplicates[Flatten[Part[#,All,1]&/@dataList]];
	data=Flatten[dataList,1];
	Table[
		{i,Plus@@Select[data,#[[1]]==i&][[All,2]]}
		,{i,x}
	]
]

End[];


(* ::Section::Closed:: *)
(*List manipulation*)


ExpressionToList::usage = "ExpressionToList[exp] returns the list of elements in the expression exp.";

Begin["`Private`"];

ExpressionToList[exp_]:=exp[[#]]&/@Range[Length[exp]]

End[];


(* ::Section::Closed:: *)
(*Matrices*)


DiagonalMatrixQ::usage = "DiagonalMatrixQ[A] returns True if A is a diagonal matrix, False otherwise.";
Reshape::usage = "Reshape[\[Psi],d1] behaves similar to Matlab's reshape, where matrix (or vector) \[Psi] is reshaped such that it has d1 rows.";

Begin["`Private`"];

DiagonalMatrixQ[A_?MatrixQ]:=DiagonalMatrix[Diagonal[A]]==A

Reshape[\[Psi]_,d1_]:=Transpose[Partition[Flatten[\[Psi]],d1]]

End[];


(* ::Section::Closed:: *)
(*Ordering*)


EigensystemOrdering::usage = "EigensystemOrdering[eigensystem] orders list result of Eigensystem by increasing eigenvalue.
EigensystemOrdering[eigensystem, n]
EigensystemOrdering[eigensystem, n, p]";

FirstLinearlyIndependent::usage = "FirstLinearlyIndependent[vecs] selects the first linearly independent vectors of list vecs.";

Begin["`Private`"];

EigensystemOrdering[es_List] := Module[
	{
	ord=Ordering[es[[1]]]
	},
	{es[[1]][[ord]],es[[2]][[ord]]}
]
EigensystemOrdering[es_List,n_Integer] := Module[
	{
	ord = Ordering[es[[1]],n]
	},
	{es[[1]][[ord]],es[[2]][[ord]]}
]
EigensystemOrdering[es_List,n_Integer,p_] := Module[
	{
	ord = Ordering[es[[1]],n,p]
	},
	{es[[1]][[ord]],es[[2]][[ord]]}
]

FirstLinearlyIndependent[vec_List] := Module[
  {a = {}, i = 1, n = Length[vec]},

  While[i <= n,
   If[
    MatrixRank[Append[a, vec[[i]]]] == Length[a] + 1,
    a = Append[a, vec[[i]]]
    ];
   i++;
   ];
  a
  ]

End[];


(* ::Section::Closed:: *)
(*Sets*)


SymmetricDifference::usage = "SymmetricDifference[A,B] returns the set of elements which are in either of the sets A or B and not in their intersection."
CircleMinus::usage = "CircleMinus[a,b] is equivalent to SymmetricDifference[a,b]";

Begin["`Private`"];

SymmetricDifference[a_,b_]:=Union[Complement[a,b],Complement[b,a]]
CircleMinus[a_,b_]:=SymmetricDifference[a,b]
CircleMinus[a_,b_,c__]:=CircleMinus[CircleMinus[a,b],c]
CircleMinus[a_]:=a

End[];


(* ::Section::Closed:: *)
(*Sums and products*)


BinaryVectorSum::usage = "BinaryVectorSum[f,i,n] performs the sum of function f[i] for i={0,...,0} to i={1,...,1}, with Length[i]=n.";
BinaryVectorProduct::usage = "BinaryVectorProduct[f,i,n] performs the product of function f[i] for i={0,...,0} to i={1,...,1}, with Length[i]=n.";
SumSet::usage = "SumSet[f, {{i, j, ...}, {{\!\(\*SubscriptBox[\"a\", \"i\"]\), \!\(\*SubscriptBox[\"a\", \"j\"]\), ...}, {\!\(\*SubscriptBox[\"b\", \"i\"]\), \!\(\*SubscriptBox[\"b\", \"j\"]\), ...}, ...}}]";

Begin["`Private`"];

BinaryVectorSum[f_,i_,n_] := Total[
	Function[i,f] /@ Tuples[{0,1},n]
]
BinaryVectorProduct[f_,i_,n_]:=Times@@(Function[i,f] /@ Tuples[{0,1},n])

SumSet[f_,list_List] := Module[
	{
	indices,n
	},

	SumSet::itlist = "Object `1` is not a vector of symbols.";
	SumSet::itsym= "Object `1` cannot be used as indices (not a list of indices).";

	If[VectorQ[list[[1]]],
		indices=list[[1]]
	,
		Message[SumSet::itlist,list[[1]]];
		Return[]
	];

	If[Count[indices,_Symbol]!=Length[indices],
		Message[SumSet::itsym,indices];
		Return[]
	];

	Plus@@(f/.(Table[indices[[n]]->#[[n]],{n,1,Length[indices]}])&/@list[[2]])
]

End[];


(* ::Section::Closed:: *)
(*Shorthands*)


ListsShorthands::usage = "ListsShorthands[] includes the Lists`Shorthands` context";

Begin["`Private`"];

ListsShorthands[]:=($ContextPath=DeleteDuplicates[Prepend[$ContextPath,"Giq`Lists`Shorthands`"]]);

End[];


Begin["`Shorthands`"];

FLI::usage = "FLI[x] is a shorthand for FirstLinearlyIndependent[x]";

End[];


Begin["`Shorthands`Private`"];

FLI[x_]:=FirstLinearlyIndependent[x]

End[];


(* ::Section::Closed:: *)
(*EndPackage*)


EndPackage[];

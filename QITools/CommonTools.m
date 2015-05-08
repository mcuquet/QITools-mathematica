(* ::Package:: *)

(* ::Title:: *)
(*QITools package: Common tools*)


(* ::Text:: *)
(*A package with common tools for Mathematica *)
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


BeginPackage["QITools`CommonTools`"];


(* ::Section::Closed:: *)
(*Simplify*)


SimplifyAbs::usage = "Applies Simplify, and at the same time tries to simplify Abs[a]^2 to a^2 if a is real";
FullSimplifyAbs::usage = "Applies FullSimplify, and at the same time tries to simplify Abs[a]^2 to a^2 if a is real";
KillTiny::usage = "KillTiny[x] sets numerical values in x (absolute) smaller than \!\(\*SuperscriptBox[\(10\), \(-6\)]\) to 0. KillTiny[x,tol] does the same for values smaller than tol."; 

Begin["`Private`"];

Options[SimplifyAbs]=Options[Simplify];
SimplifyAbs[exp_,opts:OptionsPattern[]]:=Simplify[exp,FilterRules[{opts},Options[Simplify]]]/.Abs[a_]^2:>a^2/;Simplify[a\[Element]Reals,FilterRules[{opts},Options[Simplify]]]

Options[FullSimplifyAbs]=Options[FullSimplify];
FullSimplifyAbs[exp_,opts:OptionsPattern[]]:=(FullSimplify[exp,FilterRules[{opts},Options[FullSimplify]]]/.Abs[a_]^2:>a^2/;FullSimplify[a\[Element]Reals,FilterRules[{opts},Options[FullSimplify]]])

SetAttributes[KillTiny,Listable];
KillTiny[x_,tol_:10^-6]:=If[NumericQ[x],If[Re[x]<tol,0,Re[x]]+I If[Im[x]<tol,0,Im[x]],x]

End[];


(* ::Section::Closed:: *)
(*Shorthands*)


ToolsShorthands::usage = "ToolsShorthands[] includes the CommonTools`Shorthands` context";

Begin["`Private`"];

ToolsShorthands[]:=($ContextPath=DeleteDuplicates[Prepend[$ContextPath,"CommonTools`Shorthands`"]]);

End[];


Begin["`Shorthands`"];

MF::usage = "MF is a shorthand for MatrixForm, accepting the same options.";
Options[MF]=Options[MatrixForm];
MF[x_,opts:OptionsPattern[]]:=MatrixForm[x,FilterRules[{opts},Options[MatrixForm]]]

End[];


(* ::Section::Closed:: *)
(*EndPackage*)


EndPackage[];

(* Mathematica Package *)

(* Created by the Wolfram Workbench Oct 31, 2013 *)

BeginPackage["mathSmolyak`", {"JLink`","Combinatorica`"}]
(* Exported symbols added here with SymbolName::usage *) 

chebyshevExtrema::usage="chebyshevExtrema[kk_Integer,nn_Integer]:=Cos[Pi*kk/nn]/;And[kk>0,kk<=nn]"
chebyshevPtGenerator::usage="chebyshevPtGenerator[numPts_Integer]"
chebyshevPolyGenerator::usage="chebyshevPolyGenerator[numPts_Integer]"


sparseGridPts::usage="sparseGridPts[numVars_Integer,approxLevel_Integer]"
sparseGridPolys::usage="sparseGridPts[numVars_Integer,approxLevel_Integer]"

unidimNestedGridPoints::usage="unidimNestedGridPoints[]"

unidimDisjointSetsPts::usage="unidimDisjointSetsPts[ii_Integer,ptGenerator_Function]"

unidimDisjointSetsPolys::usage="unidimDisjointSetsPolys[ii_Integer,ptGenerator_Function]"

tensorProdPts::usage="tensorProdPts[numGridPts_?listOfIntegers,ptGenerator_Function]"

tensorProdPolys::usage="tensorProdPolys[numGridPts_?listOfIntegers,ptGenerator_Function]"

xx::usage="variable for polynomials"
ii::usage="index for variable in  polynomials"

Begin["`Private`"]
(* Implementation of the package *)


chebyshevExtrema[kk_Integer,nn_Integer]:=Cos[Pi*kk/nn]/;And[kk>=0,kk<=nn,nn>0]
chebyshevExtrema[0,0]:=0

chebyshevPtGenerator=
Function[numPts,With[{nn=numPts-1},Table[chebyshevExtrema[ii,nn],{ii,00,nn}]]]

(*
chebyshevPolyGenerator=
Function[numPts,With[{nn=numPts-1},Table[ChebyshevT[ii,Unique["xx"]],{ii,00,nn}]]]
*)
chebyshevPolyGenerator=
Function[numPts,With[{nn=numPts-1},Table[ChebyshevT[ii,xx],{ii,00,nn}]]]

numSmolyakPts[ii_Integer]:=2^(ii-1)+1/;ii>=2
numSmolyakPts[1]:=1

unidimNestedGridPoints[ii_Integer,ptGenerator_Function]:=
ptGenerator[numSmolyakPts[ii]]/;ii>0

unidimNestedGridPoints[ii_Integer]:=
unidimNestedGridPoints[ii,chebyshevPtGenerator]/;ii>0


unidimNestedGridPoints[ii_Integer,ptGenerator_Function]:=
ptGenerator[numSmolyakPts[ii]]/;ii>0


unidimDisjointSetsPts[ii_Integer,ptGenerator_Function]:=
If[ii==1,unidimNestedGridPoints[1,ptGenerator],
Complement[unidimNestedGridPoints[ii,ptGenerator],
unidimNestedGridPoints[ii-1,ptGenerator]]]/;ii>0

unidimDisjointSetsPts[ii_Integer]:=
unidimDisjointSetsPts[ii,chebyshevPtGenerator]/;ii>0

unidimDisjointSetsPolys[ii_Integer,polyGenerator_Function]:=
If[ii==1,polyGenerator[1],
Complement[polyGenerator[numSmolyakPts[ii]],
polyGenerator[numSmolyakPts[ii-1]]]]/;ii>0

unidimDisjointSetsPolys[ii_Integer]:=
unidimDisjointSetsPolys[ii,chebyshevPolyGenerator]/;ii>0

tensorProdPts[numGridPts_?listOfIntegersQ,ptGenerator_Function]:=
With[{thePoints=unidimDisjointSetsPts[#,ptGenerator]&/@numGridPts},
Outer @@ {List,Sequence@@thePoints}]

tensorProdPts[numGridPts_?listOfIntegersQ]:=
tensorProdPts[numGridPts,chebyshevPtGenerator]

tensorProdPolys[numGridPolys_?listOfIntegersQ,polyGenerator_Function]:=
With[{uniqueVars=Table[xx[ii],{ii,Length[numGridPolys]}]},
With[{thePolys=MapIndexed[
(unidimDisjointSetsPolys[#,polyGenerator]/.xx->uniqueVars[[#2[[1]]]])&,
numGridPolys]},
Outer @@ {Times,Sequence@@thePolys}]]

tensorProdPolys[numGridPolys_?listOfIntegersQ]:=
tensorProdPolys[numGridPolys,chebyshevPolyGenerator]



listOfIntegersQ[theList_List]:=VectorQ[theList,IntegerQ]



rightSmolyakOuters[numVars_Integer,approxLevel_Integer]:=
With[{tooMany=
DeleteCases[
Flatten[Table[
Compositions[theSum,numVars],{theSum,numVars,numVars+approxLevel}],1],
{___,0,___}]},
tooMany]

sparseGridPts[numVars_Integer,approxLevel_Integer,ptGenerator_Function]:=
With[{RSO=rightSmolyakOuters[numVars,approxLevel]},
Flatten[tensorProdPts[#,ptGenerator]& /@ RSO,numVars]]/;And[numVars>0,approxLevel>=0]

sparseGridPts[numVars_Integer,approxLevel_Integer]:=
sparseGridPts[numVars,approxLevel,chebyshevPtGenerator]


sparseGridPolys[numVars_Integer,approxLevel_Integer,polyGenerator_Function]:=
With[{RSO=rightSmolyakOuters[numVars,approxLevel]},
Flatten[tensorProdPolys[#,polyGenerator]& /@ RSO,numVars]]/;And[numVars>0,approxLevel>=0]

sparseGridPolys[numVars_Integer,approxLevel_Integer]:=
sparseGridPolys[numVars,approxLevel,chebyshevPolyGenerator]



End[]

EndPackage[]


(* Mathematica Package *)

(* Created by the Wolfram Workbench Oct 31, 2013 *)

BeginPackage["mathSmolyak`", {"ProtectedSymbols`","JLink`"(*,"Combinatorica`"*)}]
(* Exported symbols added here with SymbolName::usage *) 
Compositions::usage="from old deprecated Combinatorica package";
KSubsets::usage="from old deprecated Combinatorica package";

xForm::usage="xform[xx,xlow,xhigh]"
xFormFromChebInterval::usage="from cheb interval"
xFormToChebInterval::usage="to cheb interval"
sparseGridPtsSubs::usage="sparseGridPtsSubs[numVars_Integer,approxLevel_Integer,ptGenerator_Function]"


numberOrSymbolQ::usage="numberOrSymbolQ[xx_]"


listOfIntegersQ::usage="listOfIntegers";
numNestedUniPts::usage="numNestedUniPts[ii_Integer]";

numDisjointUniPts::usage="numDisjointUniPts[ii_Integer]";

unidimNestedGridPoints::usage="unidimNestedGridPoints[ii_Integer,ptGenerator_Function]  implementation of section 2.2.1 nested sets of points"

unidimDisjointSetsPts::usage="unidimDisjointSetsPts[ii_Integer,ptGenerator_Function] produces disjoint sets of grid points as in section 3.2.1"

unidimDisjointSetsPolys::usage="unidimDisjointSetsPolys[ii_Integer,ptGenerator_Function] produces disjoint sets of basisfunctions as in section 3.3.1"

tensorProdDisjointPts::usage="tensorProdDisjointPts[numGridPts_?listOfIntegers,ptGenerator_Function] produces tensor products like those in table 3 section 3.2.3 for sparse grid"

tensorProdDisjointPolys::usage="tensorProdDisjointPolys[numGridPts_?listOfIntegers,ptGenerator_Function] generates disjoint sets of basis functions as in section 3.3.3"

chebyshevPolyGenerator::usage="chebyshevPolyGenerator[numPts_Integer] generates chebyshev polynomials of the first kind with xx as the variable"

chebyshevPtGenerator::usage="chebyshevPtGenerator"


sparseGridPts::usage="sparseGridPts[numVars_Integer,approxLevel_Integer] generates sparse smolyak grid using disjoint sets to produce sets of points like equations 2, 3 and 4 in section 2.2.3"

sparseGridPolys::usage="sparseGridPts[numVars_Integer,approxLevel_Integer]  generates disjoint polynomials as in section 3.3.3"


sparseGridEvalPolysAtPts::usage="sparseGridEvalPolysAtPts[numVars_Integer,approxLevel_Integer,ptGenerator_Function,polyGenerator_Function] computes the polynomials evaluation points and evaluates the polynomials at the evaluation points as in section 3.4.2"





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

tensorProdDisjointPts[numGridPts_?listOfIntegersQ,ptGenerator_Function]:=
With[{thePoints=unidimDisjointSetsPts[#,ptGenerator]&/@numGridPts},
Outer @@ {List,Sequence@@thePoints}]

tensorProdDisjointPts[numGridPts_?listOfIntegersQ]:=
tensorProdDisjointPts[numGridPts,chebyshevPtGenerator]

tensorProdDisjointPolys[numGridPolys_?listOfIntegersQ,polyGenerator_Function]:=
With[{uniqueVars=makeUniqueVars[Length[numGridPolys]]},
With[{thePolys=MapIndexed[
(unidimDisjointSetsPolys[#,polyGenerator]/.xx->uniqueVars[[#2[[1]]]])&,
numGridPolys]},
Outer @@ {Times,Sequence@@thePolys}]]


makeUniqueVars[numVars_Integer]:=
Table[xx[ii],{ii,numVars}]

tensorProdDisjointPolys[numGridPolys_?listOfIntegersQ]:=
tensorProdDisjointPolys[numGridPolys,chebyshevPolyGenerator]



listOfIntegersQ[theList_List]:=VectorQ[theList,IntegerQ]


(*implements eqn 1 conditioon*)
rightSmolyakOuters[numVars_Integer,approxLevel_Integer]:=
With[{tooMany=
compSansZeroes[numVars,approxLevel]},
tooMany]/;And[approxLevel>=0]

compSansZeroes[numVars_Integer,approxLevel_Integer]:=
DeleteCases[
Flatten[Table[
Compositions[theSum,numVars],{theSum,numVars,numVars+approxLevel}],1],
{___,0,___}]

newCompSansZeroes[numVars_Integer,approxLevel_Integer]:=
Select[
DeleteDuplicates[Flatten[Permutations/@Flatten[Table[
Partitions[theSum],{theSum,numVars,numVars+approxLevel}],1],1]],
Length[#]==numVars&]


rightSmolyakOuters[numVars_Integer,approxLevels_?listOfIntegersQ]:=
With[{tooMany=
rightSmolyakOuters[numVars,Max[approxLevels]]},
Select[tooMany,smolyakConditionFunc[approxLevels]]]/;
And[Length[approxLevels]==numVars,Min[approxLevels]>=0]

smolyakConditionFunc[approxLevels_?listOfIntegersQ]:=
Function[xx,Max[xx-(approxLevels+1)]<=0]



sparseGridPts[numVars_Integer,approxLevel_Integer,ptGenerator_Function]:=
With[{RSO=rightSmolyakOuters[numVars,approxLevel]},
Flatten[tensorProdDisjointPts[#,ptGenerator]& /@ RSO,numVars]]/;And[numVars>0,approxLevel>=0]

sparseGridPts[numVars_Integer,approxLevel_Integer]:=
sparseGridPts[numVars,approxLevel,chebyshevPtGenerator]



sparseGridPts[approxLevels_?listOfIntegersQ,ptGenerator_Function]:=
With[{numVars=Length[approxLevels]},
With[{RSO=rightSmolyakOuters[numVars,approxLevels]},
Flatten[tensorProdDisjointPts[#,ptGenerator]& /@ RSO,numVars]]]/;
And[Min[approxLevels]>=0]

sparseGridPts[approxLevels_?listOfIntegersQ]:=
sparseGridPts[approxLevels,chebyshevPtGenerator]



sparseGridPtsSubs[numVars_Integer,approxLevel_Integer,ptGenerator_Function]:=
With[{thePts=sparseGridPts[numVars,approxLevel,ptGenerator],
uniqueVars=makeUniqueVars[numVars]},
Thread[uniqueVars->#]&/@thePts]
sparseGridPtsSubs[numVars_Integer,approxLevel_Integer]:=
sparseGridPtsSubs[numVars,approxLevel,chebyshevPtGenerator]



sparseGridPtsSubs[approxLevels_?listOfIntegersQ,ptGenerator_Function]:=
With[{numVars=Length[approxLevels]},
With[{thePts=sparseGridPts[approxLevels,ptGenerator],
uniqueVars=makeUniqueVars[numVars]},
Thread[uniqueVars->#]&/@thePts]]
sparseGridPtsSubs[approxLevels_?listOfIntegersQ]:=
sparseGridPtsSubs[approxLevels,chebyshevPtGenerator]




sparseGridPolys[numVars_Integer,approxLevel_Integer,polyGenerator_Function]:=
With[{RSO=rightSmolyakOuters[numVars,approxLevel]},
Flatten[tensorProdDisjointPolys[#,polyGenerator]& /@ RSO,numVars]]/;
And[numVars>0,approxLevel>=0]

sparseGridPolys[numVars_Integer,approxLevel_Integer]:=
sparseGridPolys[numVars,approxLevel,chebyshevPolyGenerator]

numberOrSymbolQ[xx_]:=Or[NumberQ[xx],Head[xx]===Symbol]

xForm[xx_?numberOrSymbolQ, xBot_?numberOrSymbolQ, xTop_?numberOrSymbolQ] := 
 2*(xx - xBot)/(xTop - xBot) - 1

xFormToChebInterval[xx_, xBot_?numberOrSymbolQ, xTop_?numberOrSymbolQ] := 
 2*(xx - xBot)/(xTop - xBot) - 1

xFormFromChebInterval[xx_, xBot_?numberOrSymbolQ, xTop_?numberOrSymbolQ] := ((xx+1)/2)*(xTop-xBot)+xBot



sparseGridPolys[approxLevels_?listOfIntegersQ,polyGenerator_Function]:=
With[{numVars=Length[approxLevels]},
With[{RSO=rightSmolyakOuters[numVars,approxLevels]},
Flatten[tensorProdDisjointPolys[#,polyGenerator]& /@ RSO,numVars]]]/;
And[Min[approxLevels]>=0]

sparseGridPolys[approxLevels_?listOfIntegersQ]:=
sparseGridPolys[approxLevels,chebyshevPolyGenerator]





sparseGridEvalPolysAtPts[numVars_Integer,approxLevel_Integer,
ptGenerator_Function,polyGenerator_Function]:=
With[{thePolys=sparseGridPolys[numVars,approxLevel,polyGenerator],
thePts=sparseGridPts[numVars,approxLevel,ptGenerator]},
{thePts,thePolys,thePolys/.sparseGridPtsSubs[numVars,approxLevel,ptGenerator]}]
sparseGridEvalPolysAtPts[numVars_Integer,approxLevel_Integer]:=
sparseGridEvalPolysAtPts[numVars,approxLevel,
chebyshevPtGenerator,chebyshevPolyGenerator]




sparseGridEvalPolysAtPts[numVars_Integer,approxLevel_Integer,
ptGenerator_Function,polyGenerator_Function]:=
With[{thePolys=sparseGridPolys[numVars,approxLevel,polyGenerator],
thePts=sparseGridPts[numVars,approxLevel,ptGenerator]},
{thePts,thePolys,thePolys/.sparseGridPtsSubs[numVars,approxLevel,ptGenerator]}]
sparseGridEvalPolysAtPts[numVars_Integer,approxLevel_Integer]:=
sparseGridEvalPolysAtPts[numVars,approxLevel,
chebyshevPtGenerator,chebyshevPolyGenerator]





sparseGridEvalPolysAtPts[approxLevels_?listOfIntegersQ,
ptGenerator_Function,polyGenerator_Function]:=
With[{thePolys=sparseGridPolys[approxLevels,polyGenerator],
thePts=sparseGridPts[approxLevels,ptGenerator]},
{thePts,thePolys,thePolys/.
sparseGridPtsSubs[approxLevels,ptGenerator]}]

sparseGridEvalPolysAtPts[approxLevels_?listOfIntegersQ]:=
sparseGridEvalPolysAtPts[approxLevels,
chebyshevPtGenerator,chebyshevPolyGenerator]

numDisjointUniPts[ii_Integer]:=Switch[ii,
1,1,
2,2,
_ ,2^(ii-2)]/;ii>0

numNestedUniPts[ii_Integer]:=Switch[ii,
1,1,
_ ,2^(ii-1)+1]/;ii>0


(*lifted from old Combinatorica`  since full package doesn't play well with Parallel distribute*)


KS = Compile[{{n, _Integer}, {k, _Integer}}, 
             Module[{h, ss = Range[k], x},  
                    Table[(h = Length[ss]; x = n;
                           While[x === ss[[h]], h--; x--];
                           ss = Join[Take[ss, h - 1], 
                                     Range[ss[[h]]+1, ss[[h]]+Length[ss]-h+1] 
                                ]), 
                          {Binomial[n, k]-1}
                    ] 
             ]
     ]
KSubsets[l_List,0] := { {} }
KSubsets[l_List,1] := Partition[l,1]
KSubsets[l_List,2] := Flatten[Table[{l[[i]], l[[j]]}, 
                                    {i, Length[l]-1}, 
                                    {j, i+1, Length[l]}
                              ], 
                              1
                      ]
KSubsets[l_List,k_Integer?Positive] := {l} /; (k == Length[l])
KSubsets[l_List,k_Integer?Positive] := {}  /; (k > Length[l])
KSubsets[s_List, k_Integer] := Prepend[Map[s[[#]] &, KS[Length[s], k]], s[[Range[k] ]] ]

Compositions[n_Integer,k_Integer] :=
	Map[
		(Map[(#[[2]]-#[[1]]-1)&, Partition[Join[{0},#,{n+k}],2,1] ])&,
		KSubsets[Range[n+k-1],k-1]
	]



End[]


EndPackage[]




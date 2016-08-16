BeginPackage["RVarval`", {"paul`", "PackageDeveloper`", "FiniteMapping`", "numerics`"}]

ClearAll["RVarval`*", "RVarval`Private`*"]

(* -- Purpose -- *)
(*
Represent

  f: I -> R

This is a mapping variableNames -> variable values for
MachineReal valued variables.

This can be considered a special FiniteMapping or Association, Dataset, List of rules etc.

Default variable names I are {1}, {2}, {3}, etc., as in a FiniteMapping for representing
a list.

I is ordered and for some operations this order is important.
*)

(* TODO *)
(*
Less simplisitc implementation, more optimizations (sparsity)

Allow resorting inputs/outputs

Allow identifying Arrays?
 -> convert to true matrix/visualize as Table with appropriate headers, even 3D matrix/density/matrix (tensor) plot -> sparsity pattern


Maybe instead of or in addition to K x J -> R, support K -> J -> R first-class (more obvious Arrays, more uniform treatment, no
 pairing to carry along)

Check whether SparseArray or Association perform better for lots of indexed accesses.
*)

(* ^^ End ^^ *)


PublicSymbols[
  RVarval

,RVarvalMake
,RVarvalMakeConstant
,RVVDropVariableNames
,RVarvalMakePairIndexed
,RVarvalSlicePairIndexed
,RVVTimes
,RVVPlus
,RVVComponentwiseBinary
,RVVScale
,RVVComponentwiseUnary
,RVVLength
,RVVAsRules
,RVarvalAsFiniteMapping
,RVarvalMakeFromFiniteMapping
,RVVSublist
,RVVDot
,RVVDeleteOne
,RVVUpdate
  ,RVVLookupVar
,RVVLookupByVarIndex
,RVVLookupVars
,RVVLookupByVarIndices
,RVVRename
,RVVSublist
,RVVValuesMatrix
,RVVValues
,RVVVariables
,RVVDeleteMultiple
,RVVDeleteOne
  ]


Begin["`Private`"]

(* -- Purpose -- *)
(*
Head for the datastructure.
*)

(* Implementation notes *)
(*
Valid forms:

RVarval[f_FiniteMapping]
   with NumericVectorQ@FMEvaluateAll@f
*)

(* Name *)

RVarval

(* Attributes *)

RVarval~SetAttributes~HoldAllComplete

(* ^^ End ^^ *)


(* -- Purpose -- *)

(* Implementation notes *)
(*
When given names, use the other constructor because we will heavily use indexed lookup which benefits from that representation
*)


DefinePublicFunction[

RVarvalMake [x0vv : _[_[_, _?MachineNumberQ] ...]]

  ,"Create a new RVarval from a rule-list."
  ,With[{vars = First/@x0vv, vals = Last /@ x0vv}

  , RVarvalMake[vars, vals]

(* ^^ End ^^ *) ]
  ];

DefinePublicFunction[
RVarvalMakeConstant[vars_List, val_?MachineNumberQ]
  ,"maps to a single constant for all inputs"
  ,{f = FiniteMappingMakeConstant[vars, val]}~With~RVarval[f]
  ];

(* -- Purpose -- *)


DefinePublicFunction[
RVarvalMake [
  vars_List (* TODO maybe catch MachineReal numbers passed here as an error *)
, vals_?NumericVectorQ

(* Code *) ] /; Length@vars == Length@vals
  ,"Create a new RVarval from a list of variables and values"
  , With[{f = FiniteMappingMakeFromLists[vars, vals]}

  , RVarval[f]

(* ^^ End ^^ *) ]

  ];

(* -- Purpose -- *)

DefinePublicFunction[
RVVDropVariableNames[vv : RVarval[f_FiniteMapping]]
  ,"Save memory by forgetting variable names. The resulting RVV will have indexed access only."
  ,With[{g = FMForgetDomain@f}, RVarval@g]
];

(* -- Purpose -- *)
(*

*)


DefinePublicFunction[
RVarvalMakePairIndexed [PatternSequence[]
, ks_List
, l : {___RVarval}
, pairing_ : List
] /; Length@ks == Length@l
  ,"Create a new RVarval
   pairing[k_1, #]& /@ I_1 ~Union~ ...  -> R   iff reverse === True

given K (as a list) and a list of I_i -> R objects of the same length

If all I_i are the same and pairing is List, this is a function

  K x I -> R

or, with pairint == Reverse@*List

  I x K -> R"
  ,{h = FMPairing[ks, First/@l, pairing]}~With~RVarval@h
  ];

(* ^^ End ^^ *)


(* -- Purpose -- *)
DefinePublicFunction[
(* TODO would be more robust if PairIndexed is stored explicitly/abstractly, instead of unfolded *)
RVarvalSlicePairIndexed[RVarval[f_FiniteMapping], k_, pairing_ : List]
  ,"Make I_k -> R from K x U_k I_k -> R for some k in K

U denotes union

Works only for certain pairing functions (because of pattern matching)"
  ,{h=FMDomainCases[f, pairing[k,i_] :> i]}~With~RVarval@h
  ];


(* ^^ End ^^ *)


(* -- Purpose -- *)


DefinePublicFunction[
RVarvalMake [
vals_?NumericVectorQ
 ]
  ,"Create a new RVarval from a list of values.
    Variable names are generated as in FiniteMappingMakeFromList"
   , {f=FiniteMappingMakeFromList@vals}~With~RVarval@f
  ];

(* ^^ End ^^ *)


(* -- Purpose -- *)
(*

*)

DefinePublicFunction[
RVarvalMakeFromFiniteMapping[f_FiniteMapping]
  ,"Convert between FiniteMapping and RVarval"
  , RVarval[f]
  ];

DefinePublicFunction[
RVarvalAsFiniteMapping[vv : RVarval[f_FiniteMapping]]
  ,"Convert between FiniteMapping and RVarval"
  ,f
  ];

(* ^^ End ^^ *)


(* -- Purpose -- *)

DefinePublicFunction[
RVVAsRules[vv : RVarval[f_FiniteMapping]]
  ,"Convert to rule list"
  ,FMAsRules@f
];

(* ^^ End ^^ *)


(* -- Purpose -- *)

DefinePublicFunction[
RVVLength[vv : RVarval[f_FiniteMapping]] ,"Length", FMLength@f];

(* ^^ End ^^ *)

(* -- Purpose -- *)

DefinePublicFunction[
RVVComponentwiseUnary[h_, RVarval[f_FiniteMapping]]
  ,"Return g(x) := h(f(x))"
  ,With[{g = FMMapValues[h, f]},
  RVarval[g]
]
  ];


DefinePublicFunction[
RVVScale[f_RVarval, s_?MachineNumberQ]
  ,"",RVVComponentwiseUnary[#*s &, f]
  ];

(* ^^ End ^^ *)

(* -- Purpose -- *)
DefinePublicFunction[
RVVComponentwiseBinary[h : RVarval[hf_FiniteMapping], f_RVarval, binop_]
    /; RVVVariables@h == RVVVariables@f
  ,"Return g(x) := h(x) ~binop~ f(x), for h and f taking the same arguments (literally)"
  ,RVarvalMake[FMDomain@hf, Thread[RVVValues@h ~binop~ RVVValues@f]]
  ];


DefinePublicFunction[
RVVTimes[h_RVarval, f_RVarval]
  , ""
  ,RVVComponentwiseBinary[h,f,Times]
  ];

DefinePublicFunction[
RVVPlus[h_RVarval, f_RVarval]
, ""
  ,RVVComponentwiseBinary[h,f,Plus]
  ];


DefinePublicFunction[
RVVDot[x_RVarval, y_RVarval]
  ,"x: I -> R
y: I -> R

sum_i a(i) x(i)"
  ,RVVValues@x . RVVValues@y
  ];

(*
TODO the following would benefit from a more abstract/general notion of paired/multi indices
TODO but how would allowing say I -> J -> R influence existing operations?
Could we allow different J for each i even?
How to restrict it in case we don't want that?
*)
(*
Given a 'matrix'
A : J x I -> R      ('x' defined by pairing)
and a 'vector'
x: I -> R
compute

b = A.x: J -> R

as

b(j) := sum_i A(j,i) x(i)
b := sum_i A(j,i) x(i)
*)

RVVDot[Aji_RVarval, xi_RVarval,
  J_List, pairing_ (* would be nice if we didn't have to pass these in *)
] := RVVPlus (*TODO*)

(*
Given two 'matrices'
A : J x I -> R
and a 'vector'
B : I x K -> R
compute

C = A.B: J x K -> R

as

B(j, k) := sum_i A(j,i) B(i,k)
*)
RVVInner[] := Null (*TODO *)

(* ^^ End ^^ *)

DefinePublicFunction[
RVVSublist[vv_RVarval, ys_List]
  ,""
  ,  RVarvalMake[ys, RVVLookupVars[vv, ys]]
  ];

DefinePublicFunction[
RVVRename[vv_RVarval, names_List],"",    RVarvalMake[names , RVVValues@vv ]
  ];

(* -- Purpose -- *)
(*

*)

DefinePublicFunction[
RVVLookupVar[vv : RVarval[f_FiniteMapping], x_?(Not@*NumericQ)] ,"Lookup one or multiple values.", f~FMEvaluate~x
  ];
DefinePublicFunction[
RVVLookupVars[vv : RVarval[f_FiniteMapping], xs : {___?(Not@*NumericQ)}] ,"", f~FMEvaluateMultiple~xs
];
  DefinePublicFunction[
RVVLookupByVarIndex  [vv : RVarval[f_FiniteMapping], i_Integer] ,"", f~FMEvaluateIndexed~i
  ];
    DefinePublicFunction[
      RVVLookupByVarIndices[vv : RVarval[f_FiniteMapping], is : {___Integer}] ,"", f~FMEvaluateIndexedMultiple~is
    ];
(* ^^ End ^^ *)


(* -- Purpose -- *)

DefinePublicFunction[
RVVUpdate[RVarval[f_FiniteMapping], RVarval[g_FiniteMapping]]
  ,"Update or add certain values."
  ,With[{h=f~FMUpdate~g}, RVarval@h]
  ];

(* ^^ End ^^ *)


(* -- Purpose -- *)

DefinePublicFunction[
RVVDeleteOne[RVarval[f_FiniteMapping], y_]
  ,"Drop values associated with certain variables."
  ,With[{h=FMDeleteOne[f, {y}]}, RVarval@h]
  ];


DefinePublicFunction[
RVVDeleteMultiple[RVarval[f_FiniteMapping], ys_List],"",
  With[{h=FMDeleteMultiple[f, ys]}, RVarval@h]
  ];

(* ^^ End ^^ *)


(* -- Purpose -- *)
(*
*)

DefinePublicFunction[
RVVVariables[RVarval[f_FiniteMapping]] ,"Extract the variable names.", FMDomain@f];

(* ^^ End ^^ *)


(* -- Purpose -- *)

DefinePublicFunction[
RVVValues[RVarval[f_FiniteMapping]]
  ,"Extract the values"
  ,FMEvaluateAll@f
];

(* ^^ End ^^ *)

(* -- Purpose -- *)

DefinePublicFunction[

RVVValuesMatrix [RVarval[f_FiniteMapping]]
  ,"Attempt to construct a matrix from this by:
- detecting first and second varname elements by using Cases with pairing
- DeleteDuplicates on these
- index into the result set using these -- or just assume the set is sorted as specified"
  ,FMValuesMatrix[f]
];


DefinePublicFunction[
RVVValuesMatrix [RVarval[f_FiniteMapping], pairing_]  ,"", FMValuesMatrix[f, pairing]
  ];


End[];
EndPackage[];
BeginPackage["ShilovLinearAlgebra`Determinants`"]

det
detCofactor
detMinorIJ
detSumOfExpansionWithCofactors
detSumOfExpansionWithMinors

Begin["`Private`"]

(*
If we delete a row and a column from a matrix of order n, then, of course, the
remaining elements form a matrix of order n-1. The determinant of this matrix
is called a minor of the original nth-order matrix (and also a minor of its
determinant D).
*)
detMinorIJ[m_, i_, j_] :=
    det[Drop[m, {i, i}, {j, j}]]

(* val detTermsIndices : 'a list list -> ((int * int) list) list *)
detTermsIndices[m_List] := Module[
    {n, indices, rowIndices, colIndices},
    {n, n} = Dimensions[m];
    indices = Range[1, n];
    rowIndices = Permutations[indices];
    colIndices = Table[indices, n!];
    MapThread[(
        termRowIndices = #1;
        termColIndices = #2;
        MapThread[(
            termEltRow = #1;
            termEltCol = #2;
            {termEltRow, termEltCol}
            ) &,
            {termRowIndices, termColIndices}
        ]) &,
        {rowIndices, colIndices}
    ]
]

inversions[list_List] := Block[
    {$ContextPath},
    Quiet[Needs["Combinatorica`"], {General::compat}];
    Combinatorica`Inversions[list]
]

(* val detTermIndicesToTerms
     : ((int * int) list) list
    -> 'a list list
    -> 'a list
*)
detTermIndicesToTerms[termIndices_List, m_List] := Module[
    { termRowIndices
    , termElements
    , signCoeficient
    , iRow
    , jCol
    },
    termRowIndices = termIndices[[All, 1]];
    termElements = Map[({iRow, jCol} = #; m[[iRow, jCol]]) &, termIndices];
    signCoeficient = Power[-1, inversions[termRowIndices]];
    signCoeficient * (Times @@ termElements)
]

detTerms[m_List] :=
    Map[detTermIndicesToTerms[#, m] &, detTermsIndices[m]]

det[m_List] :=
    Total[detTerms[m]]

detCofactor[m_List, iRow_Integer, jCol_Integer] := Module[
    { termIndices
    , termIndicesWithIJ
    , termsWithIJ
    },
    termIndices = detTermsIndices[m];
    termIndicesWithIJ = Select[termIndices, MemberQ[#, {iRow, jCol}]&];
    termsWithIJ = Map[detTermIndicesToTerms[#, m] &, termIndicesWithIJ];
    Total[termsWithIJ] / m[[iRow, jCol]]
]

detSumOfExpansionWithCofactors[m_, {rowOrCol_, index_}] :=
    detSumOfExpansionWithCofactors[m, {rowOrCol, index, index}]

detSumOfExpansionWithCofactors[m_, {rowOrCol_, indexA_, indexB_}] := Module[
    {elements, cofactor},
    {elements, cofactor} =
        Switch[rowOrCol,
            "row", {m[[indexA, All]], detCofactor[m, indexB, #] &},
            "col", {m[[All, indexA]], detCofactor[m, #, indexB] &}
        ];
    Sum[elements[[i]] * cofactor[i], {i, Length[elements]}]
]

detSumOfExpansionWithMinors[m_, {rowOrCol_, index_}] :=
    detSumOfExpansionWithMinors[m, {rowOrCol, index, index}]

detSumOfExpansionWithMinors[m_, {rowOrCol_, indexA_, indexB_}] := Module[
    {elements, minor},
    {elements, minor} =
        Switch[rowOrCol,
            "row", {m[[indexA, All]], detMinorIJ[m, indexB, #] &},
            "col", {m[[All, indexA]], detMinorIJ[m, #, indexB] &}
        ];
    Sum[elements[[i]] * Power[-1, i + indexB] * minor[i], {i, Length[elements]}]
]

End[]
EndPackage[]

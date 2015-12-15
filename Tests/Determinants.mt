Begin["`Private`"];

{minDimension, maxDimension} = {2, 5};
{minElement  , maxElement}   = {1, 10};
{minConstant , maxConstant}  = {1, 10};
n = RandomInteger[{minDimension, maxDimension}];
i = RandomInteger[{1, n - 1}];
j = RandomInteger[{i + 1, n}];
a = RandomInteger[{minElement, maxElement}, {n, n}];
l = RandomInteger[{minConstant, maxConstant}];
m = RandomInteger[{minConstant, maxConstant}];

Protect[
    minConstant,
    maxConstant,
    minDimension,
    maxDimension,
    minElement,
    maxElement,
    n,
    i,
    j,
    a,
    l,
    m
]

Test[
(* Just a sanity check that our experiments are, at least in part, consistent
   with Mathematica's implementations.
*)
    det[a],
    Det[a],
    TestID -> "det[a] == Det[a]"
]

Test[
(* 1.41: The transposition operation.

The transpose of a determinant has the same value as the original determinant.
*)
    det[a],
    det[Transpose[a]],
    TestID -> "ch_01_41"
]

Test[
(* 1.42: The antisymmetry property.

By the property of being antisymmetric with respect to columns, we mean the
fact that a determinant changes sign when two of its columns are interchanged.

*)
    Module[
        {b},
        b = a;
        {b[[All, i]], b[[All, j]]} = {b[[All, j]], b[[All, i]]};
        det[b]
    ],
    -1 * det[a],
    TestID -> "ch_01_42"
]

Test[
(* 1.43: A determinant with two identical columns vanishes. *)
    Module[
        {b},
        b = a;
        b[[All, i]] = b[[All, j]];
        det[b]
    ],
    0,
    TestID -> "ch_01_43"
]

Test[
(* 1.44: The linear property of determinants.

    If all the elements of the jth column of a determinant D are
    "linear combinations" of two columns of numbers, i.e., if

      a[i, j] = λb[i] + μc[i]  (i = 1, 2, ... , n)

    where λ and μ are fixed numbers, then D is equal to a linear combination of
    two determinants

      D0 = λD1 + μD2
*)
    Module[
        {b, c, d, i},
        b = a;
        c = a;
        d = a;
        i = RandomInteger[{1, n}];
        c[[All, i]] = RandomInteger[{minElement, maxElement}, n];
        d[[All, i]] = RandomInteger[{minElement, maxElement}, n];
        b[[All, i]] = l * c[[All, i]] + m * d[[All, i]];
        det[b] == l * det[c] + m * det[d]
    ],
    True,
    TestID -> "ch_01_44"
]

Test[
(* 1.45. Any common factor of a column of a determinant can be factored out of
         the determinant.

Proof: If aij = λbi, then by (10) we have Dj(aij) = Dj(λbi) = λDj(bi).

*)
    Module[
        {b, i},
        i = RandomInteger[{1, n}];
        b = a;
        b[[All, i]] *= l;
        det[b]
    ],
    det[a] * l,
    TestID -> "ch_01_45"
]

Test[
(* 1.46. If a column of a determinant consists entirely of zeros, then the
         determinant vanishes.

    Proof: Since 0 is a common factor of the elements of one of the columns, we
    can factor it out of the determinant, obtaining:

        Dj(0) = Dj(0 * 1) = 0 * Dj(1) = 0
*)
    Module[
        {b, i},
        i = RandomInteger[{1, n}];
        b = a;
        b[[All, i]] = Table[0, n];
        det[b]
    ],
    0,
    TestID -> "ch_01_46"
]

Test[
(* 1.47: Addition of an arbitrary multiple of one column to another column.

The value of a determinant is not changed by adding the elements of one column
multiplied by an arbitrary number to the corresponding elements of another
column.
*)
    With[{k = j}, Module[
        {b, j},
        j = i;
        b = a;
        b[[All, j]] += b[[All, k]] * l;
        det[b]
    ]],
    det[a],
    TestID -> "ch_01_47"
]

Test[
(* 1.51: The sum of all the products of the elements of any column (or row) of
the determinant D with the corresponding cofactors is equal to the determinant
D itself.
*)
    Module[
        {i, j},
        i = RandomInteger[{1, n}];
        j = RandomInteger[{1, n}];
        {detSumOfExpansion[a, {"row", i}], detSumOfExpansion[a, {"col", j}]}
    ],
    {det[a], det[a]},
    TestID -> "ch_01_51"
]

Test[
(* 1.52: The sum of all the products of the elements of a column (or row) of
the determinant D with the cofactors of the corresponding elements of another
column (or row) is equal to zero.
*)
    Module[
        {indexRange, iA, iB, jA, jB},
        indexRange = Range[1, n];
        iA = RandomChoice[indexRange];
        iB = RandomChoice[DeleteCases[indexRange, iA]];
        jA = RandomChoice[indexRange];
        jB = RandomChoice[DeleteCases[indexRange, jA]];
        { detSumOfExpansion[a, {"row", iA, iB}]
        , detSumOfExpansion[a, {"col", jA, jB}]
        }
    ],
    {0, 0},
    TestID -> "ch_01_52"
]

Test[
(* 1.53: If we delete a row and a column from a matrix of order n, then, of
course, the remaining elements form a matrix of order n − 1. The determinant of
this matrix is called a minor of the original nth-order matrix (and also a
minor of its determinant D). If we delete the ith row and the jth column of D,
then the minor so obtained is denoted by Mij or Mij(D).

We now show that the relation (15):

    Aij = (-1)^(i + j) Mij

holds, so that the calculation of cofactors reduces to the calculation of the
corresponding minors.
*)
    Power[-1, i + j] * detMinorIJ[a, i, j],
    detCofactor[a, i, j],
    TestID -> "ch_01_53"
]

End[]
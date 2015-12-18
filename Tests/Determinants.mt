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


(*---------------------------------------------------------------------------*)
(* Sanity checks that our implementations agree with Mathematica's           *)
(*---------------------------------------------------------------------------*)

Test[
    det[a],
    Det[a],
    TestID -> "det"
]

Test[
    detMinorIJ[a, i, j],
    Reverse[Map[Reverse, Minors[a]]][[i, j]],
    TestID -> "detMinorIJ"
]


(*---------------------------------------------------------------------------*)
(* Tests for properties of determinants, in order presented in the book.     *)
(*---------------------------------------------------------------------------*)

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

      a[i, j] = lb[i] + mc[i] (i = 1, 2, ... , n)

    where l and m are fixed numbers, then D is equal to a linear combination of
    two determinants

      D0 = lD1 + mD2
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

Proof: If a[i, j] = lb[i], then by (10) we have Dj(a[i, j]) = D[j](lb[i]) = lD[j](b[i]).

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

        D[j](0) = D[j](0 * 1) = 0 * D[j](1) = 0
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
        { detSumOfExpansionWithCofactors[a, {"row", i}]
        , detSumOfExpansionWithCofactors[a, {"col", j}]
        }
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
        { detSumOfExpansionWithCofactors[a, {"row", iA, iB}]
        , detSumOfExpansionWithCofactors[a, {"col", jA, jB}]
        }
    ],
    {0, 0},
    TestID -> "ch_01_52"
]

Test[
(* 1.53: If we delete a row and a column from a matrix of order n, then, of
course, the remaining elements form a matrix of order n-1. The determinant of
this matrix is called a minor of the original nth-order matrix (and also a
minor of its determinant D). If we delete the ith row and the jth column of D,
then the minor so obtained is denoted by Mij or Mij(D).

We now show that the relation (15):

    A[i, j] = (-1)^(i + j) M[i, j]

holds, so that the calculation of cofactors reduces to the calculation of the
corresponding minors.
*)
    Power[-1, i + j] * detMinorIJ[a, i, j],
    detCofactor[a, i, j],
    TestID -> "ch_01_53"
]

Test[
(* 1.54: Expansion can now be done in terms of a minor, rather than cofactor,
    like so:

    column:
    D = (-1)^(1+j) * a[1, j] * M[1, j] + ... + (-1)^(n+j) * a[n, j] * M[n, j]

    row:
*)
    Module[
        {i, j},
        i = RandomInteger[{1, n}];
        j = RandomInteger[{1, n}];
        { detSumOfExpansionWithMinors[a, {"row", i}]
        , detSumOfExpansionWithMinors[a, {"col", j}]
        }
    ],
    {det[a], det[a]},
    TestID -> "ch_01_54"
]

End[]

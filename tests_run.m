#! /usr/bin/env MathematicaScript -script

Needs["MUnit`"]
Get["./ShilovLinearAlgebra/Determinants.m"]
If[MUnit`TestRun["./Tests/ShilovLinearAlgebraSUITE.mt"], Exit[0], Exit[1]]

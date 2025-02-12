
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(0 * x**2 + 0 * y**2 + 2 * x + 1 * y + 0 * x * y) % 5' (0, 202, 208, 218, 230, 613, 619, 632, 669, 703, 715, 816, 825, 832, 872, 879, 918, 1425, 1434, 1444, 1451, 1478, 1527, 3049, 3055, 3067, 3078, 3090, 3111, 3139, 3151, 3200, 4275, 4319, 4361, 4587, 4607, 4646)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 2 * x + y % 5» : Magma (Fin 5) where
  op := memoFinOp fun x y => 2 * x + y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly 2 * x + y % 5» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [209, 219, 231, 620, 633, 670, 704, 716, 826, 833, 873, 880, 919, 1435, 1445, 1452, 1479, 1528, 3140, 3201, 4276, 4588, 4608] [47, 99, 151, 206, 211, 212, 221, 222, 228, 229, 255, 411, 615, 616, 617, 619, 622, 623, 629, 630, 632, 639, 640, 642, 643, 666, 667, 669, 676, 677, 679, 680, 703, 706, 707, 713, 714, 818, 819, 820, 822, 823, 825, 832, 835, 836, 842, 843, 845, 846, 869, 870, 872, 879, 882, 883, 906, 907, 909, 910, 916, 917, 1020, 1223, 1427, 1428, 1429, 1431, 1432, 1434, 1441, 1442, 1444, 1451, 1454, 1455, 1478, 1481, 1482, 1488, 1489, 1491, 1492, 1515, 1516, 1518, 1519, 1525, 1526, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3051, 3052, 3053, 3055, 3058, 3059, 3065, 3066, 3069, 3075, 3076, 3078, 3102, 3103, 3105, 3106, 3113, 3115, 3116, 3139, 3142, 3143, 3149, 3150, 3253, 3456, 3659, 3862, 4065, 4268, 4269, 4270, 4272, 4273, 4275, 4283, 4284, 4290, 4291, 4293, 4314, 4321, 4343, 4380, 4583, 4584, 4585, 4587, 4590, 4591, 4598, 4599, 4605, 4606, 4629, 4635, 4636, 4658] :=
    ⟨Fin 5, «FinitePoly 2 * x + y % 5», Finite.of_fintype _, by decideFin!⟩

import LeanCompletion.UAV.LPBridge

namespace UAVProof.Case1Data

abbrev Node := Fin 53
abbrev CutIndex := Fin 32
abbrev Vehicle := Fin 3

def depot : Node := 0

-- Literal provenance is checked by certificates/bind_case1_data.py --check.
-- The external JSON binding is separate from the kernel-checked theorems below.
-- BEGIN CASE1 LITERALS
-- Case1 canonical instance SHA256: 8edfbad732afb3501d0e2616946475be39d5f5540d335d215e829a66dd8b1ac8

-- instances.json SHA256: f9b2286f61c3878629ae3f2ba1f3764133c5b8051e884a97fecb22110c7904c7

-- bound_Case1.json SHA256: d2edb19ba8e1f741c4af05a4636798520a25b219580c0102621946d2d3dd849a

def coordinates : Node → ℤ × ℤ :=
  ![(0, 0),
    (565, 575),
    (25, 185),
    (345, 750),
    (945, 685),
    (845, 655),
    (880, 660),
    (25, 230),
    (525, 1000),
    (580, 1175),
    (650, 1130),
    (1605, 620),
    (1220, 580),
    (1465, 200),
    (1530, 5),
    (845, 680),
    (725, 370),
    (145, 665),
    (415, 635),
    (510, 875),
    (560, 365),
    (300, 465),
    (520, 585),
    (480, 415),
    (835, 625),
    (975, 580),
    (1215, 245),
    (1320, 315),
    (1250, 400),
    (660, 180),
    (410, 250),
    (420, 555),
    (575, 665),
    (1150, 1160),
    (700, 580),
    (685, 595),
    (685, 610),
    (770, 610),
    (795, 645),
    (720, 635),
    (760, 650),
    (475, 960),
    (95, 260),
    (875, 920),
    (700, 500),
    (555, 815),
    (830, 485),
    (1170, 65),
    (830, 610),
    (605, 625),
    (595, 360),
    (1340, 725),
    (1740, 245)]


def required : Node → ℕ :=
  ![0,
    2,
    1,
    1,
    2,
    1,
    1,
    2,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    3,
    1,
    1,
    1,
    1,
    1,
    3,
    2,
    2,
    1,
    1,
    1,
    2,
    3,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    1,
    2,
    1,
    1,
    1,
    3,
    1,
    2,
    2,
    1,
    1,
    1,
    3,
    2,
    1]


def eqDual : Fin 106 → ℚ :=
  ![(133481501 / 2),
    (57330697 / 2),
    (84415973 / 2),
    (76818265 / 2),
    35488809,
    27976317,
    29507445,
    (93350605 / 2),
    (66718507 / 2),
    27207322,
    (51668523 / 2),
    28504385,
    18821530,
    16514144,
    20538832,
    32697628,
    (68953343 / 2),
    (86529981 / 2),
    (69993179 / 2),
    (49229751 / 2),
    (54862711 / 2),
    (85339341 / 2),
    (63312743 / 2),
    (73286741 / 2),
    (56701645 / 2),
    36062855,
    16512076,
    14207056,
    27188686,
    (86066963 / 2),
    (83823155 / 2),
    (65923659 / 2),
    (64363553 / 2),
    47468410,
    (54496277 / 2),
    (53421723 / 2),
    (53253637 / 2),
    (55831651 / 2),
    (59410845 / 2),
    (60883781 / 2),
    (53195315 / 2),
    (62356169 / 2),
    (93906415 / 2),
    49663090,
    (65179083 / 2),
    (87033249 / 2),
    (78539369 / 2),
    29852413,
    28688597,
    (66767759 / 2),
    (73471355 / 2),
    30384385,
    27849777,
    (-47079665 / 2),
    (-54093199 / 2),
    (-84350605 / 2),
    (-43067355 / 2),
    -25142691,
    -27904209,
    -28524615,
    (-87210561 / 2),
    (-49549921 / 2),
    (-35025207 / 2),
    -18885664,
    -1880000,
    -11562855,
    15972,
    4040660,
    -25476317,
    (-47394547 / 2),
    (-34733019 / 2),
    (-49892441 / 2),
    (-48965965 / 2),
    (-54418779 / 2),
    (-35923659 / 2),
    (-48111153 / 2),
    (-47976259 / 2),
    -27107459,
    -24568645,
    -11298438,
    -11893602,
    -3195699,
    (-35196037 / 2),
    (-37439845 / 2),
    (-55339341 / 2),
    (-56767759 / 2),
    -13163090,
    (-49179083 / 2),
    (-50253637 / 2),
    (-52281457 / 2),
    (-50808521 / 2),
    -26594351,
    (-44651313 / 2),
    (-52339779 / 2),
    (-53912259 / 2),
    (-78119059 / 2),
    -10968410,
    (-51168807 / 2),
    (-34229751 / 2),
    (-37808521 / 2),
    2041899,
    (-53539369 / 2),
    (-54363553 / 2),
    (-47791645 / 2),
    0,
    11351605]


def cuts : CutIndex → Finset Node :=
  ![{1, 22},
    {3, 18},
    {4, 19, 25, 33, 43, 45},
    {5, 6, 15, 38},
    {8, 41},
    {9, 10},
    {11, 12, 51},
    {13, 14, 52},
    {16, 44, 46},
    {17, 20, 21, 23, 29, 30, 31, 50},
    {24, 48},
    {26, 27, 28, 47},
    {32, 49},
    {34, 35, 36},
    {37, 39, 40},
    {1, 3, 4, 5, 6, 8, 9, 10, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 29, 30, 31, 32, 33, 41, 43, 44, 45, 46, 48, 49, 50},
    {11, 12, 13, 14, 27, 28, 51, 52},
    {26, 47},
    {34, 35},
    {36, 39, 40},
    {37, 38},
    {1, 3, 4, 5, 6, 8, 9, 10, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 29, 30, 31, 32, 33, 38, 41, 43, 44, 45, 46, 48, 49, 50},
    {11, 12, 13, 14, 26, 27, 28, 47, 51, 52},
    {34, 35, 36, 37, 39, 40},
    {1, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52},
    {34, 35, 36, 37, 38, 39, 40},
    {1, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 37, 38, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52},
    {34, 35, 36, 39, 40},
    {1, 3, 4, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 41, 43, 45, 47, 49, 50, 51, 52},
    {5, 6, 15, 16, 24, 34, 35, 36, 37, 38, 39, 40, 44, 46, 48},
    {1, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52},
    {1, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52}]


def cutDual : CutIndex → ℚ :=
  ![-4919552,
    -688690,
    0,
    0,
    -2497286,
    (-31823149 / 2),
    0,
    -13886213,
    0,
    0,
    (-5431327 / 2),
    0,
    -65844,
    0,
    0,
    0,
    0,
    -2573871,
    -929867,
    0,
    0,
    0,
    -30247115,
    (-5959375 / 2),
    0,
    (-3748343 / 2),
    0,
    -552539,
    0,
    -2457555,
    -25381237,
    -4267846]


def cutWitness : CutIndex → Node :=
  ![1,
    3,
    4,
    5,
    8,
    9,
    11,
    13,
    16,
    17,
    24,
    26,
    32,
    34,
    37,
    1,
    11,
    26,
    34,
    36,
    37,
    1,
    11,
    34,
    1,
    34,
    1,
    34,
    1,
    5,
    1,
    1]

-- END CASE1 LITERALS

/-- Python rows 0..52 are outgoing; rows 53..105 are incoming. -/
def rowEquiv : Node ⊕ Node ≃ Fin 106 := finSumFinEquiv

def degreeDual (h : Node ⊕ Node) : ℚ := eqDual (rowEquiv h)

/-- Costs and dual coefficients are in millionths of a kilometre, not kilometres.
With integer coordinates and unit_km = 1/10, the verifier's squared scale is 10^10. -/
def squaredDistance (e : Node × Node) : ℕ :=
  Int.toNat (((coordinates e.1).1 - (coordinates e.2).1)^2 +
    ((coordinates e.1).2 - (coordinates e.2).2)^2)

def costUnits (e : Node × Node) : ℚ :=
  Nat.sqrt (squaredDistance e * 10000000000)

def prescribedDegree : Node → ℕ :=
  fleetDegree (Finset.univ : Finset Vehicle) depot required

/-- A fixed rational expression, deliberately not evaluated in this module. -/
def certificateBoundUnits : ℚ :=
  LPBridge.certifiedBound prescribedDegree costUnits
    (Finset.univ : Finset CutIndex) cuts degreeDual cutDual

set_option maxRecDepth 4096 in
theorem node_count : Fintype.card Node = 53 := by decide

theorem equality_row_count : Fintype.card (Node ⊕ Node) = 106 := by decide

theorem cut_count : Fintype.card CutIndex = 32 := by decide

theorem row_out_index (i : Node) : (rowEquiv (Sum.inl i)).val = i.val := rfl

theorem row_in_index (i : Node) : (rowEquiv (Sum.inr i)).val = 53 + i.val := rfl

theorem degreeDual_out (i : Node) : degreeDual (Sum.inl i) = eqDual (Fin.castAdd 53 i) := rfl

theorem degreeDual_in (i : Node) : degreeDual (Sum.inr i) = eqDual (Fin.natAdd 53 i) := rfl

theorem arc_count : (LPBridge.arcSet (V := Node)).card = 2756 := by
  have h : LPBridge.arcSet (V := Node) = (Finset.univ : Finset Node).offDiag := by
    ext e
    simp [LPBridge.arcSet]
  rw [h, Finset.offDiag_card]
  decide

set_option maxRecDepth 4096 in
theorem inspection_count : (∑ i : Node, required i) = 72 := by decide

set_option maxRecDepth 4096 in
theorem required_positive : ∀ i : Node, i ≠ depot → 0 < required i := by decide

set_option maxRecDepth 4096 in
theorem cuts_exclude_depot : ∀ k, depot ∉ cuts k := by decide

set_option maxRecDepth 4096 in
theorem cut_witness_mem : ∀ k, cutWitness k ∈ cuts k := by decide

set_option maxRecDepth 4096 in
theorem cut_witness_positive : ∀ k, 0 < required (cutWitness k) := by decide

theorem cuts_valid (k : CutIndex) : LPBridge.ValidCut depot required (cuts k) :=
  ⟨cuts_exclude_depot k, cutWitness k, cut_witness_mem k, cut_witness_positive k⟩

set_option maxRecDepth 4096 in
theorem cutDual_nonpos : ∀ k, cutDual k ≤ 0 := by
  intro k
  fin_cases k <;> norm_num [cutDual]

theorem prescribedDegree_depot : prescribedDegree depot = 3 := by
  simp [prescribedDegree, fleetDegree]

/-- Instantiation for exactly three nonempty legal routes with exact inspection coverage.
No degree equation, capacity bound, or cut inequality is assumed here. -/
theorem three_routes_weak_duality (routes : Vehicle → LegalRoute depot)
    (hvisits : ∀ i, i ≠ depot →
      totalVisitCount Finset.univ routes i = required i) :
    certificateBoundUnits ≤ LPBridge.routeCost Finset.univ routes costUnits := by
  exact LPBridge.legalFleet_weak_duality Finset.univ routes required hvisits
    costUnits Finset.univ cuts (fun k _ => cuts_valid k)
    degreeDual cutDual (fun k _ => cutDual_nonpos k)

end UAVProof.Case1Data

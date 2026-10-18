import LeanCompletion.UAV.Case1Numerics
import LeanCompletion.UAV.Case1Fleet

namespace UAVProof.Case1Infeasible

open Case1Data Case1Budget

/-- Under the fixed Case1 distance, speed and service-time model, exact inspection
coverage by at most three nonempty legal routes violates a nine-hour time limit.
The numerical certificate is proved in Lean, not supplied as a premise. -/
theorem at_most_three_infeasible {ι : Type*} (ks : Finset ι)
    (routes : ι → LegalRoute depot)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount ks routes i = required i)
    (htime : ∀ k ∈ ks, routeTimeHours (routes k) ≤ 9) (hcard : ks.card ≤ 3) : False :=
  Case1Fleet.at_most_three_infeasible_of_certificate Case1Certificate.certificate_lower
    ks routes hvisits htime hcard

/-- A feasible finite active fleet must have at least four vehicles.
This lower bound does not formalize the separate four-vehicle feasible witness. -/
theorem feasible_fleet_card_ge_four {ι : Type*} (ks : Finset ι)
    (routes : ι → LegalRoute depot)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount ks routes i = required i)
    (htime : ∀ k ∈ ks, routeTimeHours (routes k) ≤ 9) : 4 ≤ ks.card := by
  by_contra h
  exact at_most_three_infeasible ks routes hvisits htime (by omega)

theorem one_vehicle_infeasible (routes : Fin 1 → LegalRoute depot)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount Finset.univ routes i = required i)
    (htime : ∀ k, routeTimeHours (routes k) ≤ 9) : False :=
  at_most_three_infeasible Finset.univ routes hvisits (fun k _ => htime k) (by decide)

theorem two_vehicles_infeasible (routes : Fin 2 → LegalRoute depot)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount Finset.univ routes i = required i)
    (htime : ∀ k, routeTimeHours (routes k) ≤ 9) : False :=
  at_most_three_infeasible Finset.univ routes hvisits (fun k _ => htime k) (by decide)

theorem three_vehicles_infeasible (routes : Vehicle → LegalRoute depot)
    (hvisits : ∀ i, i ≠ depot → totalVisitCount Finset.univ routes i = required i)
    (htime : ∀ k, routeTimeHours (routes k) ≤ 9) : False :=
  at_most_three_infeasible Finset.univ routes hvisits (fun k _ => htime k) (by decide)

end UAVProof.Case1Infeasible

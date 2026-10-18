
import Mathlib

namespace UAVProof

variable {V : Type*} [DecidableEq V]

/-- A directed edge, represented by its two endpoints. -/
abbrev Arc (V : Type*) := V × V

/-- The number of times an arc occurs in a route. -/
def routeFlow (route : List V) (i j : V) : ℕ :=
  (route.zip route.tail).count (i, j)

/-- Total outgoing flow at a vertex. -/
def outFlow (vertices : Finset V)
    (x : V → V → ℕ) (i : V) : ℕ :=
  ∑ j ∈ vertices, x i j

/-- Total incoming flow at a vertex. -/
def inFlow (vertices : Finset V)
    (x : V → V → ℕ) (i : V) : ℕ :=
  ∑ j ∈ vertices, x j i



/-- The outgoing and incoming occurrence counts agree
    for any nonempty closed route.- --/

theorem outFlow_eq_source_count
    [Fintype V]
    (route : List V) (i : V) :
    outFlow Finset.univ (routeFlow route) i =
      ((route.zip route.tail).map Prod.fst).count i := by

  classical
  simp only [outFlow, routeFlow]
  generalize h : route.zip route.tail = edges
  clear h
  induction edges with
  | nil =>
      simp
  | cons p ps ih =>
      obtain ⟨a, b⟩ := p
      simp only [List.map_cons]
      simp only [List.count_cons]
      simp only [Finset.sum_add_distrib]
      simp [ih]

      by_cases hai : a = i
      · have hset :
            ({x : V | a = i ∧ b = x} : Finset V) = {b} := by
          ext x
          simp [hai, eq_comm]
        rw [hset]
        simp [hai]
      · simp [hai]




/-- Number of occurrences of a vertex in a route. -/
def visitCount (route : List V) (i : V) : ℕ :=
  route.count i



/-- Incoming flow equals the number of target occurrences. -/
theorem inFlow_eq_target_count
    [Fintype V]
    (route : List V) (i : V) :
    inFlow Finset.univ (routeFlow route) i =
      ((route.zip route.tail).map Prod.snd).count i := by
  classical
  simp only [inFlow, routeFlow]
  generalize h : route.zip route.tail = edges
  clear h
  induction edges with
  | nil =>
      simp
  | cons p ps ih =>
      obtain ⟨a, b⟩ := p
      simp only [List.map_cons]
      simp only [List.count_cons]
      simp only [Finset.sum_add_distrib]
      simp [ih]
      by_cases hbi : b = i
      · have hset :
            ({x : V | a = x ∧ b = i} : Finset V) = {a} := by
          ext x
          simp [hbi, eq_comm]
        rw [hset]
        simp [hbi]
      · simp [hbi]



/-- Counts in the first and second components of consecutive
    edges differ only by the endpoints of the route. -/

theorem route_endpoint_count_balance
    (route : List V) (i : V) :
    ((route.zip route.tail).map Prod.fst).count i
      + route.getLast?.toList.count i
    =
    ((route.zip route.tail).map Prod.snd).count i
      + route.head?.toList.count i := by
  induction route with
  | nil =>
      simp

  | cons a rest ih =>
      cases rest with
      | nil =>
          simp
      | cons b tail =>
          have hfirst :
              ((a :: b :: tail).zip (b :: tail)).map Prod.fst =
                a :: ((b :: tail).zip tail).map Prod.fst := by
            simp
          have hsecond :
              ((a :: b :: tail).zip (b :: tail)).map Prod.snd =
                b :: ((b :: tail).zip tail).map Prod.snd := by
            simp

          simp only [List.tail_cons] at ih ⊢
          rw [hfirst, hsecond]
          simp only [List.count_cons]
          simp only [List.head?_cons] at ih ⊢
          simp only [List.getLast?_cons_cons] at ih ⊢

          have hsingle (v : V) :
              List.count i ((some v).toList) =
                (if (v == i) = true then 1 else 0) := by
            simp [List.count_cons]

          rw [hsingle b] at ih
          rw [hsingle a]
          omega




/-- A closed route has equal incoming and outgoing flows
    at every vertex. -/
theorem closed_route_flow_balance
    [Fintype V]
    (route : List V)
    (hclosed : route.head? = route.getLast?)
    (i : V) :
    outFlow Finset.univ (routeFlow route) i =
      inFlow Finset.univ (routeFlow route) i := by
  rw [outFlow_eq_source_count, inFlow_eq_target_count]
  have h := route_endpoint_count_balance route i
  rw [← hclosed] at h
  omega










end UAVProof

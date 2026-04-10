import Mathlib

def insertionSort (l : List Int) : List Int := sorry

theorem insertionSort_sorted (l : List Int) :
    List.Sorted (· ≤ ·) (insertionSort l) := sorry

theorem insertionSort_perm (l : List Int) :
    insertionSort l ~ l := sorry

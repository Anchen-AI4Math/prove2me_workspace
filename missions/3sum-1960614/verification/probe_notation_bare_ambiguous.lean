import Lean
namespace A
def seq := Nat.add
end A
namespace B
def seq := Nat.add
end B
infixr:30 " ;; " => A.seq
infixr:30 " ;; " => B.seq
set_option profiler true in
def probe : Nat := 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1 ;; 1

/-
**Lane-word stores into a buffer, source side**: the source facts at `let w
= asLanes sg wd K in let o = xchg b[i] w in e` (`xchgAt` on a buffer of
lanes with a constant lane word) that the exchange rows of
`Spike/Lib/Seg.lean` (`Out.holdLoad`, `Out.xchgStore`) ask, and the source
memory's latest messages around a fresh buffer and the exchanges into it.

The target half is in place: the lowered load and store are
`holdLd_ndW`/`xchgSt_ndW` (`Spike/Lib/A64AllocNodes.lean`), and the
consumer matches the store by the source exchange (`src_swap_step_cfg`,
`Spike/Lib/SrcMem.lean`) under the store row of the memory relation. What
it needs from the source, here:

- `accs_lanes`: a lanes element is one word.
- `localStep_asLanes_lit`: `let w = asLanes sg wd K` binds the word
  `K mod 2^64` (a local step, taken by a block).
- `xchgSite_lanes`: `let o = xchg b[i] v in e`, `b` a locative to a buffer
  of lanes, is an exchange site (`XchgSite`) of the element's address.
- `evalAt_cons_ne`, `evalAt_lit`: evaluation in an environment extended by
  another name, and of a literal.
- `valRep_elem`, `valRep_num`: the element's address word and the lane
  word represent the target address and value.
- `sLatest_push_self`, `sLatest_push_other`: the latest message after one
  more; `sLatest_allocBuf`: after a buffer allocation, word `i`'s latest
  message is its zero message.
- `laneStore`: the whole store's source side: the `asLanes` local step to
  an exchange site of element `i`, with the address and stored word
  represented.
-/
import Spike.Lib.Form
import Scc.Sem.RowsAlloc

namespace Spike.Lib.LaneStoreSrc

open CoreLang CoreTerm TermRun
open Scc.Sem (ValRep wordAddr)
open Scc.Sem.MemRel (SLatest)

/-! ## Terms and environments -/

/-- A lanes element is one word. -/
theorem accs_lanes (sg : Bool) (wd : Wd) : accs (.lanes sg wd) = some [.one] := rfl

/-- A literal evaluates to its number. -/
theorem evalAt_lit (env : Env) (n : Nat) : evalAt env (.lit n) = some (.intS (.lit n), [cst (.num n)]) := rfl

/-- The number of a literal's word. -/
theorem numOf_lit (n : Nat) : numOf [cst (.num n)] = some n := rfl

/-- A variable other than the newest binding evaluates as before it. -/
theorem evalAt_cons_ne (env : Env) {y x : String} (ty : Ty) (ws : List Word) (h : x ≠ y) :
    evalAt ((y, ty, ws) :: env) (.var x) = evalAt env (.var x) := by
  have : (y == x) = false := by simp [Ne.symm h]
  simp [evalAt, lookupE, List.find?, this]

/-- The newest binding evaluates to its words. -/
theorem evalAt_cons_self (env : Env) (y : String) (ty : Ty) (ws : List Word) :
    evalAt ((y, ty, ws) :: env) (.var y) = some (ty, ws) := by
  simp [evalAt, lookupE, List.find?]

/-- **`let w = asLanes sg wd K`** of a literal binds the lane word
`K mod 2^64` (a local step). -/
theorem localStep_asLanes_lit {p : Prog} {c : Spike.Lib.Ctl} {x : String} {sg : Bool} {wd : Wd} {K : Nat}
    {e : Expr} (ht : c.term = .let_ x (.asLanes sg wd (.lit K)) e) :
    Spike.Lib.LocalStep p c ⟨e, (x, .lanes sg wd, [cst (.num (K % W64))]) :: c.env, none⟩ :=
  Spike.Lib.Form.localStep_asLanes (n := K) ht rfl rfl

/-- **An exchange of a lanes element is an exchange site**: at `let o =
xchg b[i] v in e` with `b` an untagged locative to `sb`, of a buffer type
whose elements are lanes, the site exchanges the element's address
`offs sb i`. -/
theorem xchgSite_lanes {c : Spike.Lib.Ctl} {x : String} {b v : At} {i : Nat} {e : Expr} {t : Ty} {pw : Word}
    {μ : Mode} {sg : Bool} {wd : Wd} {sb : WeakMem.Address}
    (ht : c.term = .let_ x (.xchgAt b (.lit i) v) e) (hb : evalAt c.env b = some (t, [pw]))
    (hpw : pw.val = .loc sb 0) (hbuf : bufElem t = some (μ, .lanes sg wd)) :
    Spike.Lib.XchgSite c x (offs sb i) (.lanes sg wd) v e :=
  ⟨accs_lanes sg wd, .inr ⟨b, .lit i, t, pw, _, _, μ, sb, i, ht, hb, hpw, hbuf, rfl, rfl, rfl⟩⟩

/-! ## Representation -/

/-- **The address word of element `i`** of a buffer at label `l` placed at
`A` represents `A + 8 i`. -/
theorem valRep_elem {lbl : WeakMem.AllocLabel → Option Nat} {l : WeakMem.AllocLabel} {A : Nat}
    (hl : lbl l = some A) (i : Nat) : ValRep lbl (.loc (offs ⟨l, 0⟩ i) 0) (A + 8 * i) :=
  ⟨by decide, A + 8 * i, by simp [wordAddr, offs, hl], rfl⟩

/-- A number below `2^64` represents itself. -/
theorem valRep_num (lbl : WeakMem.AllocLabel → Option Nat) {K : Nat} (hK : K < 2 ^ 64) :
    ValRep lbl (.num K) K :=
  ⟨hK, rfl⟩

/-! ## Latest messages -/

/-- The message just pushed is the latest at its address. -/
theorem sLatest_push_self (sm : WeakMem.Memory) (m : WeakMem.Msg) : SLatest (sm.push m) m.loc sm.size := by
  refine ⟨⟨m, by simp, rfl⟩, fun k m' hk hm' => ?_⟩
  rw [Array.getElem?_push] at hm'
  split at hm'
  · omega
  · rw [Array.getElem?_eq_none (by omega)] at hm'; cases hm'

/-- A push to another address keeps the latest message. -/
theorem sLatest_push_other {sm : WeakMem.Memory} {sa : WeakMem.Address} {j : Nat} (h : SLatest sm sa j)
    {m : WeakMem.Msg} (hne : m.loc ≠ sa) : SLatest (sm.push m) sa j := by
  obtain ⟨⟨m0, hm0, hl⟩, hlast⟩ := h
  have hj : j < sm.size := (Array.getElem?_eq_some_iff.mp hm0).1
  refine ⟨⟨m0, ?_, hl⟩, fun k m' hk hm' => ?_⟩
  · rw [Array.getElem?_push]
    split
    · omega
    · exact hm0
  rw [Array.getElem?_push] at hm'
  split at hm'
  · cases hm'; exact hne
  · exact hlast k m' hk hm'

/-- **After a buffer allocation**, word `i` (`i < n`) of the label has its
zero message, at `|mem| + i`, as its latest. -/
theorem sLatest_allocBuf (lbl : WeakMem.AllocLabel) (n : Nat) (zero : Option (List WeakMem.Val)) (s : St)
    {i : Nat} (hi : i < n) :
    SLatest (allocBuf lbl n zero s).1.mem ⟨lbl, i⟩ (s.mem.size + i) := by
  refine ⟨⟨_, Scc.Sem.allocBuf_mem_new lbl n zero s hi, rfl⟩, fun k m hk hm => ?_⟩
  have hsz := Scc.Sem.allocBuf_mem_size lbl n zero s
  have hk' : k < s.mem.size + n := by
    have := (Array.getElem?_eq_some_iff.mp hm).1; omega
  obtain ⟨d, rfl⟩ : ∃ d, k = s.mem.size + d := ⟨k - s.mem.size, by omega⟩
  rw [Scc.Sem.allocBuf_mem_new lbl n zero s (by omega)] at hm
  cases hm
  intro h
  have : d = i := congrArg WeakMem.Address.offset h
  omega

/-! ## A lane-word store -/

/-- **A lane-word store into element `i` of a buffer**, source side: at
`let w = asLanes sg wd K in let o = xchg b[i] w in e`, `b` bound (not
shadowed by `w`) to an untagged locative to label `l`, placed at `A`, of a
buffer of lanes, and `K < 2^64`: the `asLanes` is a local step to a control
`c1` at an exchange site of element `i` (address `A + 8 i`), holding
nothing, whose exchanged word `w` is the number `K`, which represents `K`.
These are the source premises of `Out.holdLoad` and `Out.xchgStore` at the
lowered load and store of the element. -/
theorem laneStore {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {c : Spike.Lib.Ctl}
    {w o b : String} {sg : Bool} {wd : Wd} {K i : Nat} {e : Expr} {t : Ty} {pw : Word} {μ : Mode}
    {l : WeakMem.AllocLabel} {A : Nat}
    (ht : c.term = .let_ w (.asLanes sg wd (.lit K)) (.let_ o (.xchgAt (.var b) (.lit i) (.var w)) e))
    (hwb : b ≠ w) (hb : evalAt c.env (.var b) = some (t, [pw])) (hpw : pw.val = .loc ⟨l, 0⟩ 0)
    (hbuf : bufElem t = some (μ, .lanes sg wd)) (hl : lbl l = some A) (hK : K < 2 ^ 64) :
    let c1 : Spike.Lib.Ctl := ⟨.let_ o (.xchgAt (.var b) (.lit i) (.var w)) e,
      (w, .lanes sg wd, [cst (.num K)]) :: c.env, none⟩
    Spike.Lib.LocalStep p c c1 ∧ Spike.Lib.XchgSite c1 o (offs ⟨l, 0⟩ i) (.lanes sg wd) (.var w) e ∧
      ValRep lbl (.loc (offs ⟨l, 0⟩ i) 0) (A + 8 * i) ∧ c1.hold = none ∧
      evalAt c1.env (.var w) = some (.lanes sg wd, [cst (.num K)]) ∧ ValRep lbl (cst (.num K)).val K := by
  intro c1
  have hmod : K % W64 = K := Nat.mod_eq_of_lt hK
  refine ⟨?_, xchgSite_lanes rfl (by rw [evalAt_cons_ne _ _ _ hwb]; exact hb) hpw hbuf, valRep_elem hl i, rfl,
    evalAt_cons_self _ _ _ _, valRep_num lbl hK⟩
  have h := localStep_asLanes_lit (p := p) ht
  rw [hmod] at h
  exact h

end Spike.Lib.LaneStoreSrc

import WeakCore.TermMainDefs

/-!
# TermOwnG0Defs: the G-0 contract and the post-publish freeze (shared defs)

A planting promise `B` of thread `i` (index `cP.mem.size`, address `a0`, value `v0`, view
`w < cP.mem.size`) names its root `r` (`v0 = .loc a' g`, `a'.label = r`; `r` own and unpublished at
`cP`). `SoloNP` is `Solo` without a thread step at a `publish` naming `r`. `G0Win` (the G-0 contract):
along such a run from the plant, every certified configuration has `vWr ≤ w`. `PostPubFreeze`: after a
`publish` naming `r`, the run does no `bufInit` at the labels `L` (the cells planted from `r`).
-/

namespace TermOwnG0Defs

open CoreLang CoreTerm TermRun TermStep
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The thread is at a `publish` whose reference names `r`. -/
def PubAt (th : TTh) (r : AllocLabel) : Prop :=
  ∃ (y : String) (a : At) (e : Expr) (rt : Ty) (ws : List Word) (ad : Address),
    th.term = .let_ y (.publish a) e ∧ evalAt th.env a = some (rt, ws) ∧ ws.map (·.val) = [.loc ad 0] ∧
      ad.label = r

/-- `Solo` without a thread step at a `publish` naming `r`. -/
inductive SoloNP (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (r : AllocLabel) : Cfg → Cfg → Prop
  | refl (c) : SoloNP p k arch i r c c
  | thread {c c' c''} : c' ∈ threadSteps p k arch c i → (∀ th, c.ths[i]? = some th → ¬ PubAt th r) →
      SoloNP p k arch i r c' c'' → SoloNP p k arch i r c c''
  | prom {c c''} (a v w) : w < c.mem.size → SoloNP p k arch i r (promise c i a v w) c'' →
      SoloNP p k arch i r c c''

theorem SoloNP.toSolo {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {r : AllocLabel} {c c' : Cfg}
    (h : SoloNP p k arch i r c c') : Solo p k arch i c c' := by
  induction h with
  | refl => exact .refl _
  | thread hs _ _ ih => exact .thread hs ih
  | prom a v w hw _ ih => exact .prom a v w hw ih

/-- **The G-0 contract** for the planting promise `promise cP i a0 v0 w` with root `r`: before a
`publish` naming `r`, every certified configuration of the run has `vWr ≤ w`. -/
def G0Win (p : Prog) (k : Promises.Knobs) (arch : Arch) (cP : Cfg) (i : Nat) (a0 : Address)
    (v0 : WeakMem.Val) (w : Ts) (r : AllocLabel) : Prop :=
  ∀ c th, SoloNP p k arch i r (promise cP i a0 v0 w) c → Certified p k arch c i → c.ths[i]? = some th →
    th.vs.vWr ≤ w

/-- **The post-publish freeze** at labels `L`: from a `publish` naming `r` reached by `SoloNP`, the
continuation does no `bufInit` at `L`. -/
def PostPubFreeze (p : Prog) (k : Promises.Knobs) (arch : Arch) (cP : Cfg) (i : Nat) (a0 : Address)
    (v0 : WeakMem.Val) (w : Ts) (r : AllocLabel) (L : AllocLabel → Prop) : Prop :=
  ∀ c th c' c1 th1, SoloNP p k arch i r (promise cP i a0 v0 w) c → c.ths[i]? = some th → PubAt th r →
    c' ∈ threadSteps p k arch c i → Solo p k arch i c' c1 → Certified p k arch c1 i → c1.ths[i]? = some th1 →
    ∀ l, L l → ¬ BufInitOn th1 l

end TermOwnG0Defs

#print axioms TermOwnG0Defs.SoloNP.toSolo

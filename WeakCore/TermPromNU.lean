import WeakCore.TermPlantP

/-!
# TermPromNU: no outstanding promise is `undef` (the `SysInvN.promNU` clause)

`PromNotUndef c` (every outstanding promise of every thread is a non-`undef`
message) is carried by `SysInvN`.  It holds vacuously at a promise-free
configuration (`SysInvW.toN`), is kept by a thread step (messages are never
rewritten, and the stepper's promises only shrink: `tstep_appUp`), and by a
promise step: the new promise is certified, and a certified promise is not
`undef` (`certified_promNotUndefX`, at the promiser's `InvAtX` as in
`TermPlantP.privSlot_of`, under `CertRunP`).
-/

namespace TermPromNU
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- **A thread step keeps `PromNotUndef`** (outstanding promises lie in memory, `AllPromLt`). -/
theorem promNU_thread {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (h : PromNotUndef c) (hplt : AllPromLt c) (hc : c' ∈ threadSteps p k arch c i) : PromNotUndef c' := by
  obtain ⟨th, r, hth, hr, e1, -, e3, ho⟩ := threadSteps_upd hc
  obtain ⟨-, hme, hsub, -, -⟩ := TermCert.tstep_appUp hr
  have old : ∀ (q : Nat) (thq : TTh) (t : Ts) (m : Msg), c.ths[q]? = some thq → t ∈ thq.promises → c'.mem[t]? = some m → m.val ≠ .undef := by
    intro q thq t m hq ht hm
    have hlt : t < c.mem.size := hplt q thq t hq ht
    obtain ⟨m0, hm0⟩ : ∃ m0, c.mem[t]? = some m0 := ⟨c.mem[t], Array.getElem?_eq_getElem hlt⟩
    have h1 : r.1[t]? = some m0 := hme t m0 hm0
    rw [e1, h1] at hm
    cases hm
    exact h q thq t _ hq ht hm0
  intro q thq t m hq ht hm
  by_cases hqi : q = i
  · subst hqi
    rw [e3] at hq; cases hq
    exact old q th t m hth (hsub t ht) hm
  · rw [ho q hqi] at hq
    exact old q thq t m hq ht hm

/-- **A promise step keeps `PromNotUndef`**: the new promise is certified. -/
theorem promNU_prom {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (h : PromNotUndef c) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : PromNotUndef (promise c j a v w) := by
  obtain ⟨S0, hSS0⟩ := X.inv.thr j th X.hth
  obtain ⟨-, hTE, hm, -⟩ := id hSS0
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hSC : StoClo (Cut Eg j S0) := fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  obtain ⟨th0, E, hth0, hx, hTE0, hm0, hSC0, hbo0, hfb, hfr, -, -, -, hIH0⟩ := InvAtXF_of (p := p) (k := k) (arch := arch)
    hpi.2.1 hTE (by rw [gOf_promise, hpi.2.2]; exact MemInv_promSt hm) hSC (by rw [gOf_promise]; exact X.inv.bf)
    (by rw [hpi.2.2]; exact TermTyped.riniCoh_promSt (X.inv.riniCoh _ _ _ X.hth))
    (fun l cl f hs hp => Nat.le_trans (X.inv.frlt l cl f (cutSto_sub hs) hp)
      (Nat.sub_le_sub_right (by rw [hpi.1]; show c.mem.size ≤ (c.mem.push _).size; rw [Array.size_push]; exact Nat.le_succ _) 1))
  have hX : InvAtX p k arch j (Cut Eg j S0) _ _ (promise c j a v w) :=
    ⟨th0, E, hth0, hx, hTE0, hm0, hSC0, hbo0, hfb, hfr, fun _ _ _ h => h.elim, hIH0⟩
  have hsc := fun c1 h1 h2 => (hrun X S0 hSS0 c1 h1 h2).1
  have hwin := fun c1 h1 h2 => (hrun X S0 hSS0 c1 h1 h2).2
  intro q thq t m hq ht hmt
  by_cases hqj : q = j
  · subst hqj
    have ht' : t ∈ TermFul.promsOf (promise c q a v w) q := by
      rw [TermFul.promsOf_some hq]; exact ht
    exact (certified_promNotUndefX (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') hwin hX X.cert ht' hmt).1
  · rw [promise_other X.hth hqj] at hq
    have hlt : t < c.mem.size := X.inv.plt q thq t hq ht
    rw [hpi.1] at hmt
    have e : (c.mem.push ⟨a, v, w⟩)[t]? = c.mem[t]? := by
      rw [Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt]
    exact h q thq t m hq ht (by rw [← e]; exact hmt)

#print axioms promNU_thread
#print axioms promNU_prom

end TermPromNU

/-
**The worker's certified promises** (data in
`Spike/Lib/WakeW1.lean`, `Spike/Lib/WakeW1Compat.lean`).

A promise of the worker is certified by a run of the worker alone under the
certification semantics. From the worker's invariant (`CInv`: a pair of
`Wi` with the control invariant, the `G` values of the messages not
promised) every step of that run is one of the rows (`WSide.closed`): it
keeps memory and promises, or writes a `Good` message (in the worker's
footprint, in a shared region, a `G` value, one word wide, `1` at `cT`);
it writes `cT` only at the store, from before the store point
(`cstep_shape`). So every promise the run fulfils is `Good`, and the run
fulfils at most one promise of `cT`, none past the store (`cstep`). A
certified promise is then out of every placed label (the source stutters)
or the promise of `c`'s `1` before the store with no `c` message yet (the
source promises `kc`; `post_prom1`).

- `countP_erase_le`, `countP_erase_of_false`: counting after `erase`.
- `certOkC_pot`: a potential bound over a certifying run.
- `stepOne_rmw_casesG`: `stepOne_rmw_casesR` with the read not promised.
- `CInv`, `Good`, `Past`: the certification run's invariant, a message
  the worker may write, the source worker past its store.
- `cstep_shape`, `cstep`: one certification step from `CInv`; `cntT`,
  `passB`: the potential and its bound.
- `prom_good`: a certified promise is `Good`, of `cT` only before the
  store point with no other promise of `cT`.
- `post_prom1`: the promise row keeps `Post`.
-/
import Spike.Lib.WakeW1Store

namespace Spike.Lib.WakeW1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt
open Spike.Lib.WorkerSrcStep

/-! ## Generic facts -/

/-- Erasing one element lowers a count by at most one. -/
theorem countP_erase_le {α : Type} [DecidableEq α] (f : α → Bool) (a : α) :
    ∀ l : List α, l.countP f ≤ (l.erase a).countP f + 1
  | [] => by simp
  | b :: l => by
    have ih := countP_erase_le f a l
    rw [List.erase_cons]
    by_cases h : b = a
    · subst h; simp only [beq_self_eq_true, ite_true, List.countP_cons]; split <;> omega
    · simp only [beq_iff_eq, h, ite_false, List.countP_cons]; split <;> omega

/-- Erasing an element the predicate rejects keeps the count. -/
theorem countP_erase_of_false {α : Type} [DecidableEq α] (f : α → Bool) {a : α} (ha : f a = false) :
    ∀ l : List α, (l.erase a).countP f = l.countP f
  | [] => by simp
  | b :: l => by
    have ih := countP_erase_of_false f ha l
    rw [List.erase_cons]
    by_cases h : b = a
    · subst h; simp [ha]
    · simp only [beq_iff_eq, h, ite_false, List.countP_cons, ih]

/-- **A potential bound over a certifying run**: if every step from `P`
lands in `P` and moves `f` down by no less than `B` (`f x + B y ≤ f y +
B x`), and `f` vanishes with no promise, then `f ≤ B` at every certifiable
`P` configuration. -/
theorem certOkC_pot {I : ISA} {A : Arch} {cs : CertSem I} {tid : Nat} {P : Thread I × Memory → Prop}
    (f B : Thread I × Memory → Nat) (hf : ∀ x, x.1.prom = [] → f x = 0)
    (hs : ∀ x y, P x → ThreadStepC A cs tid x y → P y ∧ f x + B y ≤ f y + B x)
    {t : Thread I} {mem : Memory} (hp : P (t, mem)) (hc : CertOkC A cs tid t mem) : f (t, mem) ≤ B (t, mem) := by
  obtain ⟨t', mem', hr, he⟩ := hc
  suffices key : ∀ x y, ThreadNPC A cs tid x y → y.1.prom = [] → P x → f x ≤ B x from key _ _ hr he hp
  intro x y hr
  induction hr with
  | refl x => intro he _; rw [hf x he]; exact Nat.zero_le _
  | step hxy _ ih =>
    intro he hpx
    obtain ⟨hpy, hle⟩ := hs _ _ hpx hxy
    have := ih he hpy
    omega

/-- **An RMW's outcomes, with no cover** (`stepOne_rmw_casesR`), the write
read not promised. -/
theorem stepOne_rmw_casesG {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {k : RmwKind} {noRet : Bool} {a : Nat} {op : Val → Option Val} {g : Val → I.State}
    (hex : I.exec t.st = some (.rmw k noRet (wordLoc a) op fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hpl : ∀ p ∈ t.prom, p ≤ mem.last) :
    ∃ old tr, o.thread.st = g old ∧ mem.read? (wordLoc a) tr = some old ∧ tr ∉ t.prom ∧
      ((op old = none ∧ o.mem = mem ∧ o.thread.prom = t.prom) ∨
       (∃ new, op old = some new ∧
        ((∃ q ∈ t.prom, mem.get? q = some ⟨wordLoc a, new, tid⟩ ∧ o.mem = mem ∧ o.thread.prom = t.prom.erase q) ∨
          (o.mem = (mem.append ⟨wordLoc a, new, tid⟩).1 ∧ o.thread.prom = t.prom)))) := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff A tid hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
  rw [Lower.run_rmw_iff] at hr
  obtain ⟨tr, old, c1, hx, rfl, hcase⟩ := hr
  obtain ⟨hm0, hp0⟩ := rmwFenceOpt_mem_prom A
    ({ views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] } : Kraken.Promising.Ctx)
  have hnp : tr ∉ t.prom := by
    obtain ⟨ts', v', he, -, -, -, hp⟩ := (mem_readSuccs A).mp hx
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -, -⟩ := he
    rw [hp0] at hp
    intro hmem
    have : t.prom.contains tr = true := List.elem_eq_true_of_mem hmem
    exact absurd this (by simpa using hp)
  obtain ⟨v, hrd, hvo, hce⟩ := readSuccs_shape A _ hx
  have hm1 : c1.mem = mem := (congrArg Ctx.mem hce).trans hm0
  have hp1 : c1.prom = t.prom := (readSuccs_prom A _ hx).trans hp0
  simp only at hvo hrd
  subst hvo
  rw [hm0] at hrd
  refine ⟨old, tr, finishInstr_st hth, hrd, hnp, ?_⟩
  rw [(finishInstr_relKey hth).1, hm]
  rcases hcase with ⟨hop, rfl⟩ | ⟨new, c2, hop, hw, rfl⟩
  · obtain ⟨h1, h2⟩ := rmwFenceOpt_mem_prom A c1
    exact .inl ⟨hop, h1.trans hm1, h2.trans hp1⟩
  · refine .inr ⟨new, hop, ?_⟩
    obtain ⟨h1, h2⟩ := rmwFenceOpt_mem_prom A
      (Lower.rmwBump (A.rmwKind k) noRet (wordLoc a) { c2 with rmwWrote := true })
    obtain ⟨h3, h4⟩ := rmwBump_mem_prom (A.rmwKind k) noRet (wordLoc a) { c2 with rmwWrote := true }
    rw [h1, h3, h2, h4]
    simp only
    rcases (Lower.mem_writeSuccs_iff A tid _).mp hw with ⟨q, hq, hg, -, rfl⟩ | ⟨-, rfl⟩
    · rw [hp1] at hq
      rw [hm1] at hg
      refine .inl ⟨q, hq, hg, hm1, ?_⟩
      show c1.prom.erase q = _
      rw [hp1]
    · refine .inr ⟨?_, ?_⟩
      · show (c1.mem.append _).1 = _
        rw [hm1]
      · show (c1.prom ++ [c1.mem.last + 1]).erase (c1.mem.last + 1) = t.prom
        rw [hm1, hp1]
        exact List.erase_append_singleton_self fun hmem => by
          have h1 : @LE.le Nat instLENat (mem.last + 1) mem.last := hpl _ hmem
          omega

/-! ## The certification run's invariant -/

/-- **The source worker is past its store** (at `wkUnpark` or `ret `). -/
def Past (c : Ctl) : Prop := c.term = wkUnpark ∨ c.term = .ret .unit

/-- **The certification run's invariant** at the ghost record `w`: the
worker's state paired with a control in `Wi` under the control invariant,
the messages not promised and the initial values `G` values, the promises
in memory. -/
structure CInv (Q : WakeRel) (D : WSide Q.ι) (w : Q.ι) (x : Thread isaLSE2 × Memory) : Prop where
  wi : ∃ c, D.Wi w x.1.st c ∧ WCtl (D.cw w) c
  msgs : MsgsExcept (fun m => Q.G w m.loc m.val) x.1.prom x.2
  init : ∀ l, Q.G w l (x.2.initVal l)
  le : ∀ p ∈ x.1.prom, p ≤ x.2.last

/-- **A message the worker may write**: in its footprint, in a shared
region, a `G` value, one word wide, of a 64-bit value, `1` at `cT`. -/
def Good (Q : WakeRel) (Λ : Scc.Sem.Layout) (w : Q.ι) (m : Msg) : Prop :=
  (Q.P w).foot 1 m.loc ∧ Consumer1.LocIn Λ.shared m.loc ∧ Q.G w m.loc m.val ∧ m.loc.bytes = 8 ∧
    m.val.toNat < 2 ^ 64 ∧ (m.loc = (Q.C w).cT → m.val = 1)

/-- The worker's terms that are bindings: its store and its unpark. -/
theorem wterm_let {e : Expr} (h : WTerm e) {x : String} {op : Op} {e' : Expr} (he : e = .let_ x op e') :
    e = wkStore ∨ e = wkUnpark := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  · simp [wkTail] at he
  · simp [wkBody] at he
  · exact .inl rfl
  · exact .inr rfl
  · simp at he

variable {Q : WakeRel} {D : WSide Q.ι} {μ : Marks} {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch} {w : Q.ι}

/-- **One certification step of the worker from `CInv`, by the rows**: from
a control `c` to a control `c'` (both in `Wi`, `c'` under the control
invariant), it keeps memory and promises and the store point, or writes a
`Good` message (appended, or fulfilling a promise of it): off `cT` keeping
the store point, at `cT` from before it to past it. -/
theorem cstep_shape (hC : WCompat Q D μ Λ arch) (hx : WCompatX Q D)
    (hcTin : InLabel (Q.SR w).lbl (Q.SR w).lsize (Q.C w).cT) {k : KState} {x y : Thread isaLSE2 × Memory}
    (hq : CInv Q D w x) (hs : ThreadStepC Arch.armv8 (certSem abi Arch.armv8 μ k 1) 1 x y) :
    ∃ c c', D.Wi w x.1.st c ∧ D.Wi w y.1.st c' ∧ WCtl (D.cw w) c' ∧
      ((y.2 = x.2 ∧ y.1.prom = x.1.prom ∧ (Past c' ↔ Past c)) ∨
       ∃ L V, Good Q Λ w ⟨L, V, 1⟩ ∧
         ((y.2 = (x.2.append ⟨L, V, 1⟩).1 ∧ y.1.prom = x.1.prom) ∨
          (∃ q ∈ x.1.prom, x.2.get? q = some ⟨L, V, 1⟩ ∧ y.2 = x.2 ∧ y.1.prom = x.1.prom.erase q)) ∧
         (L ≠ (Q.C w).cT → (Past c' ↔ Past c)) ∧ (L = (Q.C w).cT → ¬ Past c ∧ Past c')) := by
  obtain ⟨c, hwi, hctl⟩ := hq.wi
  obtain ⟨outs, o, hso, ho, rfl⟩ := hs
  have hcw := hC.cwv w
  have hsite := hC.noSite w _ _ hwi
  have hown : ∀ s, (D.ms w).own s = [] := fun s => by rw [hC.own w, hx.own1 w]
  have hmpG : ∀ a V, (D.ms w).mp (wordLoc a) true → Q.G w (wordLoc a) V → V.toNat < 2 ^ 64 →
      Good Q Λ w ⟨wordLoc a, V, 1⟩ ∧ wordLoc a ≠ (Q.C w).cT := by
    intro a V hmp hG hf
    obtain ⟨hf1, hout, hin⟩ := hC.mpW w _ hmp
    have hne : wordLoc a ≠ (Q.C w).cT := fun e => hout (by rw [e]; exact hcTin)
    exact ⟨⟨hf1, hin, hG, rfl, hf, fun e => absurd e hne⟩, hne⟩
  have hpast : ∀ {c'}, LocalRun wakeSrc c c' → (Past c' ↔ Past c) := fun hr => localRun_pass hcw hr hctl
  have hkeep : ∀ {c'}, LocalRun wakeSrc c c' → D.Wi w o.thread.st c' → o.mem = x.2 → o.thread.prom = x.1.prom →
      ∃ c c', D.Wi w x.1.st c ∧ D.Wi w (o.thread, o.mem).1.st c' ∧ WCtl (D.cw w) c' ∧
        (((o.thread, o.mem).2 = x.2 ∧ (o.thread, o.mem).1.prom = x.1.prom ∧ (Past c' ↔ Past c)) ∨
         ∃ L V, Good Q Λ w ⟨L, V, 1⟩ ∧
           (((o.thread, o.mem).2 = (x.2.append ⟨L, V, 1⟩).1 ∧ (o.thread, o.mem).1.prom = x.1.prom) ∨
            (∃ q ∈ x.1.prom, x.2.get? q = some ⟨L, V, 1⟩ ∧ (o.thread, o.mem).2 = x.2 ∧
              (o.thread, o.mem).1.prom = x.1.prom.erase q)) ∧
           (L ≠ (Q.C w).cT → (Past c' ↔ Past c)) ∧ (L = (Q.C w).cT → ¬ Past c ∧ Past c')) :=
    fun hr hX hm hp => ⟨c, _, hwi, hX, localRun_wCtl hcw hr hctl, .inl ⟨hm, hp, hpast hr⟩⟩
  cases hat : abi.atSys x.1.st
  · rw [certSem_step_of_not_site hsite hat] at hso
    cases D.closed w _ _ hwi with
    | outL hl =>
      cases hl with
      | out r =>
        cases r with
        | silent s' c' he hr hX =>
          obtain ⟨hm, hp, hst⟩ := stepOne_silent_keep he (Lower.silentTree_done s') hso ho
          exact hkeep hr (hst ▸ hX) hm hp
        | choice P tree he hsil hX =>
          obtain ⟨hm, hp, hP⟩ := stepOne_silent_keep he hsil hso ho
          obtain ⟨c', hr, hX'⟩ := hX _ hP
          exact hkeep hr hX' hm hp
        | load kl A g x' a e ty w' he ht =>
          rcases wterm_let hctl.term ht with h | h <;> rw [h] at ht <;> simp [wkStore, wkUnpark] at ht
        | store kr A V s' x' a b e ty tb wa wb he ht hea hva heb hvb hX htag =>
          have hst : c.term = wkStore := by
            rcases wterm_let hctl.term ht with h | h
            · exact h
            · rw [h] at ht; simp [wkUnpark] at ht
          have hnps : ¬ PreSplit c.term := by
            rw [hst]; rintro (hp | hp) <;> simp [wkStore, wkTail, wkBody] at hp
          have hcj := hctl.cj hnps
          have hnp : ¬ Past c := by
            unfold Past; rw [hst]; rintro (hp | hp) <;> simp [wkStore, wkUnpark] at hp
          rw [hst] at ht
          simp only [wkStore, Expr.let_.injEq] at ht
          obtain ⟨rfl, hop, rfl⟩ := ht
          simp only [Op.store.injEq, true_and, and_true] at hop
          obtain ⟨rfl, rfl⟩ := hop
          obtain ⟨cty, cμ, cu, hcv, hcell, hcu⟩ := hcj.1
          have hwa : wa = D.cw w := by
            rw [hcv] at hea; simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea
            exact hea.2.symm
          subst hwa
          obtain ⟨a', hcT, hcTa, hcTo⟩ := hC.cT w
          rw [hC.cwv w, hC.lbl w] at hva
          obtain ⟨-, x0, hx0, hA⟩ := hva
          rw [hcTa] at hx0; cases hx0
          have hA' : A = BitVec.ofNat 64 a' := by
            apply BitVec.eq_of_toNat_eq
            have := A.isLt
            simp only [BitVec.toNat_ofNat]
            omega
          subst hA'
          simp only [TermRun.evalAt, Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at heb
          obtain ⟨-, rfl⟩ := heb
          have hV : V = 1 := by
            apply BitVec.eq_of_toNat_eq
            change 1 < 2 ^ 64 ∧ V.toNat = 1 at hvb
            rw [hvb.2]; rfl
          subst hV
          have he' : isaLSE2.exec x.1.st = some (.store kr false (wordLoc a') 1 fun _ => .done s') := he
          obtain ⟨hst', hc⟩ := stepOne_store_cases Arch.armv8 he' hso ho hq.le
          have hgood : Good Q Λ w ⟨wordLoc a', 1, 1⟩ :=
            ⟨by rw [← hcT]; exact hC.cTfoot w, by rw [← hcT]; exact hC.cTin w, by rw [← hcT]; exact hx.Gc w,
              rfl, show (1 : Val).toNat < 2 ^ 64 by decide, fun _ => rfl⟩
          refine ⟨c, ⟨wkUnpark, ("d", .unit, []) :: c.env, none⟩, hwi, hst' ▸ hX, ⟨rfl, .inr (.inr (.inr (.inl rfl))), fun hp => ?_,
            fun _ => envCJ_cons hcj _ _⟩, .inr ⟨wordLoc a', 1, hgood, ?_, fun hne => absurd hcT.symm hne,
            fun _ => ⟨hnp, .inl rfl⟩⟩⟩
          · exfalso; rcases hp with hp | hp <;> simp [wkUnpark, wkTail, wkBody] at hp
          · rcases hc with ⟨q, hq', hg, -, hm, hp⟩ | ⟨hm, hp⟩
            · exact .inr ⟨q, hq', hg, hm, hp⟩
            · exact .inl ⟨hm, hp⟩
        | rtStore kr L V s' c' he hrt hmp hG hr hX =>
          have hwide := hC.wide w _ _ hwi
          have hL8 : L.bytes = 8 := (Scc.Cert.WideA64.execLSE2_w8 hwide he).1
          have hfit : V.toNat < 2 ^ 64 := (Scc.Cert.WideA64.execLSE2_fit hwide he).1
          rw [hC.G w] at hG
          obtain ⟨a, rfl⟩ : ∃ a, L = wordLoc a := ⟨_, ExtRows.loc_wordLoc hL8⟩
          obtain ⟨hst, hc⟩ := stepOne_store_cases Arch.armv8 he hso ho hq.le
          obtain ⟨hgood, hne⟩ := hmpG a V hmp hG hfit
          refine ⟨c, c', hwi, hst ▸ hX, localRun_wCtl hcw hr hctl,
            .inr ⟨wordLoc a, V, hgood, ?_, fun _ => hpast hr, fun e => absurd e hne⟩⟩
          rcases hc with ⟨q, hq', hg, -, hm, hp⟩ | ⟨hm, hp⟩
          · exact .inr ⟨q, hq', hg, hm, hp⟩
          · exact .inl ⟨hm, hp⟩
        | rtLoad kl L g c' he hrt hmp hr hX =>
          obtain ⟨hm, hp⟩ := stepOne_load_keep he hso ho
          obtain ⟨v, hst, hG⟩ := stepOne_load_msgsExcept (G := Q.G w) he hso ho hq.msgs hq.init
          rw [← hC.G w] at hG
          refine hkeep hr ?_ hm hp
          rw [hst]; exact hX v hG fun u hu => by simp [hown] at hu
        | rtRmw k' L op g c' he hrt hmp hr hX =>
          have hwide := hC.wide w _ _ hwi
          have hL8 : L.bytes = 8 := (Scc.Cert.WideA64.execLSE2_w8 hwide he).1
          have hfit : ∀ old v, op old = some v → v.toNat < 2 ^ 64 := (Scc.Cert.WideA64.execLSE2_fit hwide he).1
          obtain ⟨a, rfl⟩ : ∃ a, L = wordLoc a := ⟨_, ExtRows.loc_wordLoc hL8⟩
          obtain ⟨old, tr, hst, hrd, hn, hc⟩ := stepOne_rmw_casesG Arch.armv8 he hso ho hq.le
          have hGo := msgsExcept_read (G := Q.G w) hq.msgs hq.init hrd hn
          rw [← hC.G w] at hGo
          obtain ⟨hGn, hXo⟩ := hX old hGo (fun u hu => by simp [hown] at hu)
          rcases hc with ⟨-, hm, hp⟩ | ⟨new, hop, hc⟩
          · exact hkeep hr (hst ▸ hXo) hm hp
          · have hGn' := hGn new hop
            rw [hC.G w] at hGn'
            obtain ⟨hgood, hne⟩ := hmpG a new hmp hGn' (hfit old new hop)
            refine ⟨c, c', hwi, hst ▸ hXo, localRun_wCtl hcw hr hctl,
              .inr ⟨wordLoc a, new, hgood, ?_, fun _ => hpast hr, fun e => absurd e hne⟩⟩
            rcases hc with ⟨q, hq', hg, hm, hp⟩ | ⟨hm, hp⟩
            · exact .inr ⟨q, hq', hg, hm, hp⟩
            · exact .inl ⟨hm, hp⟩
        | sys K call hK ha =>
          rw [hC.K w] at hK; cases hK; rw [hat] at ha; cases ha
        | holdLoad kl A g x' sa u v e he hxs =>
          obtain ⟨-, ⟨a, t', pw, μ', ht, -⟩ | ⟨b, i, t', pw, ti, iws, μ', sb, k', ht, -⟩⟩ := hxs <;>
            rcases wterm_let hctl.term ht with h | h <;> rw [h] at ht <;> simp [wkStore, wkUnpark] at ht
        | xchgStore kr A V s' x' sa u v e tv wv wold he hxs =>
          obtain ⟨-, ⟨a, t', pw, μ', ht, -⟩ | ⟨b, i, t', pw, ti, iws, μ', sb, k', ht, -⟩⟩ := hxs <;>
            rcases wterm_let hctl.term ht with h | h <;> rw [h] at ht <;> simp [wkStore, wkUnpark] at ht
        | ctrRmw k' op g x' τ e n he hrt hm hs =>
          rcases hs with ⟨a, -, -, ht, -⟩ | ⟨-, a, -, ht, -⟩ <;>
            rcases wterm_let hctl.term ht with h | h <;> rw [h] at ht <;> simp [wkStore, wkUnpark] at ht
        | alloc s' A x' a τ e ta ws k' wold old us he ht =>
          rcases wterm_let hctl.term ht with h | h <;> rw [h] at ht <;> simp [wkStore, wkUnpark] at ht
        | newStore kr A V s' x' a t e w' wold old _ he hm ht =>
          rcases wterm_let hctl.term ht with h | h <;> rw [h] at ht <;> simp [wkStore, wkUnpark] at ht
        | emit K buf n Pw Qw hK ha =>
          rw [hC.K w] at hK; cases hK; rw [hat] at ha; cases ha
        | fence k' s' c' he hr hX =>
          obtain ⟨hst, hm, hp⟩ := stepOne_fence_eq Arch.armv8 he hso ho
          cases hr with
          | loc hr => exact hkeep hr (hst ▸ hX) hm hp
          | pub _ hps _ =>
            -- the worker's terms publish nothing
            obtain ⟨-, -, x', a, e, t, t', ws, hpt, -⟩ := hps
            rcases hpt with ⟨ht, -⟩ | ⟨r, ht, -⟩ <;>
              rcases wterm_let hctl.term ht with h | h <;> rw [h] at ht <;> simp [wkStore, wkUnpark] at ht
      | ldSt kl A g x' a e ty w' V he ht =>
        rcases wterm_let hctl.term ht with h | h <;> rw [h] at ht <;> simp [wkStore, wkUnpark] at ht
    | unpk k' A B op g x' a e ty jw he hrt hmp hop ht hh hev hv hA hX =>
      have hst : c.term = wkUnpark := by
        rcases wterm_let hctl.term ht with h | h
        · rw [h] at ht; simp [wkStore] at ht
        · exact h
      have hnps : ¬ PreSplit c.term := by
        rw [hst]; rintro (hp | hp) <;> simp [wkUnpark, wkTail, wkBody] at hp
      have hcj := hctl.cj hnps
      rw [hst] at ht
      simp only [wkUnpark, Expr.let_.injEq] at ht
      obtain ⟨rfl, -, rfl⟩ := ht
      have hL : (⟨A, 8⟩ : Loc) = wordLoc A.toNat := ExtRows.loc_wordLoc rfl
      rw [hL] at he hmp hX
      obtain ⟨old, tr, hst', hrd, hn, hc⟩ := stepOne_rmw_casesG Arch.armv8 he hso ho hq.le
      have hGo := msgsExcept_read (G := Q.G w) hq.msgs hq.init hrd hn
      rw [← hC.G w] at hGo
      obtain ⟨hG1, hXo⟩ := hX old hGo (fun u hu => by simp [hown] at hu)
      rw [hC.G w] at hG1
      rcases hc with ⟨hop', -⟩ | ⟨new, hop', hc⟩
      · rw [hop old] at hop'; cases hop'
      have hn1 : new = 1 := by rw [hop old] at hop'; exact (Option.some.inj hop').symm
      subst hn1
      obtain ⟨hgood, hne⟩ := hmpG _ 1 hmp hG1 (show (1 : Val).toNat < 2 ^ 64 by decide)
      refine ⟨c, ⟨.ret .unit, ("w", ExtName.unpark.sig.2, []) :: c.env, none⟩, hwi, hst' ▸ hXo,
        ⟨rfl, .inr (.inr (.inr (.inr rfl))), fun hp => ?_, fun _ => ?_⟩,
        .inr ⟨_, 1, hgood, ?_, fun _ => ⟨fun _ => .inl hst, fun _ => .inr rfl⟩, fun e => absurd e hne⟩⟩
      · exfalso; rcases hp with hp | hp <;> simp [wkTail, wkBody] at hp
      · simpa [EnvCJ, TermRun.evalAt, TermRun.lookupE, List.find?_cons] using hcj
      · rcases hc with ⟨q, hq', hg, hm, hp⟩ | ⟨hm, hp⟩
        · exact .inr ⟨q, hq', hg, hm, hp⟩
        · exact .inl ⟨hm, hp⟩
    | texit K a hK ha =>
      rw [hC.K w] at hK; cases hK; rw [hat] at ha; cases ha
    | fnc k' s' c' he hr hX =>
      obtain ⟨hst, hm, hp⟩ := stepOne_fence_eq Arch.armv8 he hso ho
      exact hkeep hr (hst ▸ hX) hm hp
  · cases D.closed w _ _ hwi with
    | outL hl =>
      cases hl with
      | out r =>
        cases r with
        | sys K call hK ha hd hok hX =>
          rw [hC.K w] at hK; cases hK
          obtain ⟨hm, hp, hmem⟩ := certSem_step_sys hsite ha hd hok.2.1 hso ho
          obtain ⟨c', hr, hX'⟩ := hX _ hmem
          exact hkeep hr hX' hm hp
        | emit K buf n Pw Qw hK ha hd =>
          rw [hC.K w] at hK; cases hK
          rcases hC.sysOk w _ _ _ hwi ha hd with h | ⟨hnw, -⟩
          · cases h
          · exact absurd rfl (hnw 1 buf n)
        | choice P tree he hsil hX =>
          obtain ⟨m, rfl⟩ := hC.sysExec w _ _ _ hwi hat he
          cases hsil
        | _ =>
          obtain ⟨m, hm⟩ := hC.sysExec w _ _ _ hwi hat ‹isaLSE2.exec x.1.st = some _›
          cases hm
      | ldSt _ _ _ _ _ _ _ _ _ he =>
        obtain ⟨m, hm⟩ := hC.sysExec w _ _ _ hwi hat he
        cases hm
    | unpk _ _ _ _ _ _ _ _ _ _ he =>
      obtain ⟨m, hm⟩ := hC.sysExec w _ _ _ hwi hat he
      cases hm
    | texit K a hK ha hd =>
      rw [hC.K w] at hK; cases hK
      obtain ⟨-, -, hmem⟩ := certSem_step_sys hsite ha hd (fun _ _ => nofun) hso ho
      simp [certSuccs, results] at hmem
    | fnc _ _ _ he =>
      obtain ⟨m, hm⟩ := hC.sysExec w _ _ _ hwi hat he
      cases hm

/-- The worker's promises of `cT` messages: the potential of `cstep`. -/
def cntT (cT : Loc) (x : Thread isaLSE2 × Memory) : Nat :=
  x.1.prom.countP fun p => decide ((x.2.get? p).map Msg.loc = some cT)

open Classical in
/-- `1` before the target store point, `0` past it: the bound of `cstep`. -/
noncomputable def passB (Q : WakeRel) (w : Q.ι) (x : Thread isaLSE2 × Memory) : Nat :=
  if (Q.C w).passT x.1.st then 0 else 1

/-- **One certification step of the worker from `CInv`**: it lands in
`CInv`, every promise it fulfils is of a `Good` message, and it lowers the
count of promises of `cT` by no more than it lowers `passB` (a `cT` write
passes the store point). -/
theorem cstep (hC : WCompat Q D μ Λ arch) (hx : WCompatX Q D)
    (hcTin : InLabel (Q.SR w).lbl (Q.SR w).lsize (Q.C w).cT) {k : KState} {x y : Thread isaLSE2 × Memory}
    (hq : CInv Q D w x) (hs : ThreadStepC Arch.armv8 (certSem abi Arch.armv8 μ k 1) 1 x y) :
    CInv Q D w y ∧ (∀ p ∈ x.1.prom, p ∉ y.1.prom → ∀ m, x.2.get? p = some m → Good Q Λ w m) ∧
      cntT (Q.C w).cT x + passB Q w y ≤ cntT (Q.C w).cT y + passB Q w x := by
  obtain ⟨c, c', hwi, hwi', hctl', hcase⟩ := cstep_shape (Λ := Λ) hC hx hcTin hq hs
  have hB0 : ∀ {z : Thread isaLSE2 × Memory} {cz : Ctl}, D.Wi w z.1.st cz → Past cz → passB Q w z = 0 :=
    fun h hp => by unfold passB; rw [ite_eq_left ((hC.pass w _ _ h).mpr hp)]
  have hB1 : ∀ {z : Thread isaLSE2 × Memory} {cz : Ctl}, D.Wi w z.1.st cz → ¬ Past cz → passB Q w z = 1 :=
    fun h hp => by unfold passB; rw [ite_eq_right fun h' => hp ((hC.pass w _ _ h).mp h')]
  have hBle : passB Q w y ≤ 1 := by
    by_cases hp : Past c'
    · rw [hB0 hwi' hp]; omega
    · rw [hB1 hwi' hp]; exact Nat.le_refl 1
  have hBe : (Past c' ↔ Past c) → passB Q w y = passB Q w x := fun hi => by
    by_cases hp : Past c
    · rw [hB0 hwi hp, hB0 hwi' (hi.mpr hp)]
    · rw [hB1 hwi hp, hB1 hwi' fun h => hp (hi.mp h)]
  rcases hcase with ⟨hm, hp, hpi⟩ | ⟨L, V, hg, hw, hne, heq⟩
  · refine ⟨⟨⟨c', hwi', hctl'⟩, msgsExcept_of_eq hq.msgs hm hp, by rw [hm]; exact hq.init,
      by rw [hm, hp]; exact hq.le⟩, fun p hp1 hp2 => absurd (hp ▸ hp1) hp2, ?_⟩
    have hf : cntT (Q.C w).cT y = cntT (Q.C w).cT x := by unfold cntT; rw [hm, hp]
    have hb := hBe hpi
    omega
  · by_cases hL : L = (Q.C w).cT
    · obtain ⟨hnp, hpp⟩ := heq hL
      have hbx : passB Q w x = 1 := hB1 hwi hnp
      rcases hw with ⟨hm, hp⟩ | ⟨q, hqp, hgq, hm, hp⟩
      · refine ⟨⟨⟨c', hwi', hctl'⟩, hm ▸ hp ▸ msgsExcept_append hq.msgs hg.2.2.1,
          fun l => by rw [hm, (Memory.Prefix.append _ _).initVal]; exact hq.init l,
          fun p hp1 => ?_⟩, fun p hp1 hp2 => absurd (hp ▸ hp1) hp2, ?_⟩
        · rw [hp] at hp1; rw [hm, Memory.last_append]; exact Nat.le_succ_of_le (hq.le p hp1)
        · have hf : cntT (Q.C w).cT y = cntT (Q.C w).cT x := by
            unfold cntT; rw [hp]
            apply List.countP_congr
            intro p hp1
            rw [hm, (Memory.Prefix.append _ _).get? (hq.le p hp1)]
          omega
      · refine ⟨⟨⟨c', hwi', hctl'⟩, hm ▸ hp ▸ msgsExcept_erase hq.msgs hgq hg.2.2.1,
          by rw [hm]; exact hq.init, fun p hp1 => by rw [hp] at hp1; rw [hm]; exact hq.le p (List.mem_of_mem_erase hp1)⟩,
          fun p hp1 hp2 m hgm => ?_, ?_⟩
        · have hpq : p = q := Classical.byContradiction fun hpq =>
            hp2 (by rw [hp]; exact (List.mem_erase_of_ne hpq).mpr hp1)
          subst hpq; rw [hgq] at hgm; cases hgm; exact hg
        · have hby : passB Q w y = 0 := hB0 hwi' hpp
          have hf : cntT (Q.C w).cT x ≤ cntT (Q.C w).cT y + 1 := by
            unfold cntT; rw [hp, hm]; exact countP_erase_le _ _ _
          omega
    · have hb := hBe (hne hL)
      rcases hw with ⟨hm, hp⟩ | ⟨q, hqp, hgq, hm, hp⟩
      · refine ⟨⟨⟨c', hwi', hctl'⟩, hm ▸ hp ▸ msgsExcept_append hq.msgs hg.2.2.1,
          fun l => by rw [hm, (Memory.Prefix.append _ _).initVal]; exact hq.init l,
          fun p hp1 => ?_⟩, fun p hp1 hp2 => absurd (hp ▸ hp1) hp2, ?_⟩
        · rw [hp] at hp1; rw [hm, Memory.last_append]; exact Nat.le_succ_of_le (hq.le p hp1)
        · have hf : cntT (Q.C w).cT y = cntT (Q.C w).cT x := by
            unfold cntT; rw [hp]
            apply List.countP_congr
            intro p hp1
            rw [hm, (Memory.Prefix.append _ _).get? (hq.le p hp1)]
          omega
      · refine ⟨⟨⟨c', hwi', hctl'⟩, hm ▸ hp ▸ msgsExcept_erase hq.msgs hgq hg.2.2.1,
          by rw [hm]; exact hq.init, fun p hp1 => by rw [hp] at hp1; rw [hm]; exact hq.le p (List.mem_of_mem_erase hp1)⟩,
          fun p hp1 hp2 m hgm => ?_, ?_⟩
        · have hpq : p = q := Classical.byContradiction fun hpq =>
            hp2 (by rw [hp]; exact (List.mem_erase_of_ne hpq).mpr hp1)
          subst hpq; rw [hgq] at hgm; cases hgm; exact hg
        · have hf : cntT (Q.C w).cT y = cntT (Q.C w).cT x := by
            unfold cntT; rw [hp, hm]
            apply countP_erase_of_false
            simp [hgq, hL]
          omega

/-! ## The promise row -/

variable {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **A certified promise of the worker is `Good`, and of `cT` only before
the store point with no other promise of `cT`**: from `CInv` at the
promising configuration, `cstep` gives `StepG` (`certOkC_prom_good_cfg`)
and the potential bound (`certOkC_pot`). -/
theorem prom_good (hC : WCompat Q D μ Λ arch) (hx : WCompatX Q D) (hwf : Λ.WF)
    (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) {m : Msg}
    (hc : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 1) 1 (Live.Sem.promThread t1 t.1.mem m)
      (t.1.mem.append m).1) :
    Good Q Λ w m ∧ cntT (Q.C w).cT (Live.Sem.promThread t1 t.1.mem m, (t.1.mem.append m).1) ≤
      passB Q w (Live.Sem.promThread t1 t.1.mem m, (t.1.mem.append m).1) := by
  have hcTin : InLabel (Q.SR w).lbl (Q.SR w).lsize (Q.C w).cT := by
    obtain ⟨a', hcT, hx', ho⟩ := hC.cT w
    rw [hcT]; exact inLabel_wordLoc h.core.mem hwf hx' ho
  have hq : CInv Q D w (Live.Sem.promThread t1 t.1.mem m, (t.1.mem.append m).1) :=
    { wi := ⟨Ctl.of s1, h.pt1.1, h.wCtl⟩
      msgs := msgsExcept_promise (Scc.Sem.MemInv.msgsExcept h.core.memInv _) m
      init := fun l => by
        show Q.G w l ((t.1.mem.append m).1.initVal l)
        rw [(Memory.Prefix.append _ _).initVal]; exact h.core.memInv.1 l
      le := fun p hp => by
        show p ≤ (t.1.mem.append m).1.last
        rw [Memory.last_append]
        rcases List.mem_append.mp hp with hp | hp
        · exact Nat.le_succ_of_le (h.prom_le p hp)
        · rw [List.mem_singleton.mp hp]; exact Nat.le_refl _ }
  have hG : StepG Arch.armv8 (certSem abi Arch.armv8 μ t.2 1) 1 (CInv Q D w) (Good Q Λ w) :=
    fun x y hx' hs _ => ⟨(cstep hC hx hcTin hx' hs).1, (cstep hC hx hcTin hx' hs).2.1⟩
  refine ⟨certOkC_prom_good_cfg hG hq hc (p := t.1.mem.last + 1) (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    (Scc.Sem.Memory.get?_append_new), ?_⟩
  exact certOkC_pot (P := CInv Q D w) (cntT (Q.C w).cT) (passB Q w)
    (fun x hx' => by unfold cntT; rw [hx']; rfl)
    (fun x y hx' hs => ⟨(cstep hC hx hcTin hx' hs).1, (cstep hC hx hcTin hx' hs).2.2⟩) hq hc

/-- **The worker's certified promise keeps `Post`**: the promised message
is `Good` (`prom_good`). Off `cT` it is out of every placed label and the
source stutters (`post_local`); at `cT` it is the worker's `1` before its
store with no `c` message yet, and the source worker promises `kc`
(`prom_c_src`, `cProtS_prom`). -/
theorem post_prom1 (hC : WCompat Q D μ Λ arch) (hx : WCompatX Q D) (hwf : Λ.WF)
    (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hex : SrcSem.mainExit s = []) {m : Msg} (hwt : m.tid = 1)
    (hc : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 1) 1 (Live.Sem.promThread t1 t.1.mem m)
      (t.1.mem.append m).1) :
    ∃ s', (wakeS arch).Run s [] s' ∧
      Q.Post Λ (t.1.withThread 1 (Live.Sem.promThread t1 t.1.mem m) (t.1.mem.append m).1, t.2) s' := by
  obtain ⟨⟨hf, hin, hG, hb8, hfit, hv1⟩, hcnt⟩ := prom_good hC hx hwf h hc
  have hT0 := ((cProt_iff _ _ _).mp h.prot).1
  have hpl := h.prom_le
  have hlast : (t.1.mem.append m).1.last = t.1.mem.last + 1 := Memory.last_append _ _
  have hnew : (t.1.mem.append m).2 = t.1.mem.last + 1 := rfl
  have hstk : s1.stack = [] := h.pt1.2.1
  have hown' : ExtRows.OwnOk ((fun i => if i = 0 then Q.own w 0 t0.st s0.stack
      else Q.own w 1 (Live.Sem.promThread t1 t.1.mem m).st s1.stack) 1) (t.1.mem.append m).1
      (Live.Sem.promThread t1 t.1.mem m).prom := fun L v hm => by
    simp [hstk, hx.own1] at hm
  have hdisj : ∀ L v v', (L, v) ∈
      (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1.st s1.stack) 0 →
      (L, v') ∈ (fun i => if i = 0 then Q.own w 0 t0.st s0.stack
        else Q.own w 1 (Live.Sem.promThread t1 t.1.mem m).st s1.stack) 1 → False := fun L v v' _ h1 => by
    simp [hstk, hx.own1] at h1
  have hocov : ∀ L v, (L, v) ∈ (fun i => if i = 0 then Q.own w 0 t0.st s0.stack
      else Q.own w 1 (Live.Sem.promThread t1 t.1.mem m).st s1.stack) 1 → (Q.P w).cov 1 L := fun L v h1 => by
    simp [hstk, hx.own1] at h1
  have hb : (Live.Sem.promThread t1 t.1.mem m).Bnd (t.1.mem.append m).1.last := by
    have hle : t.1.mem.last ≤ (t.1.mem.append m).1.last := by rw [hlast]; exact Nat.le_succ _
    exact ⟨h.core.bnd1.views.mono hle, h.core.bnd1.regs.mono hle⟩
  have hcov : CohCoversL (Live.Sem.promThread t1 t.1.mem m).views (Live.Sem.promThread t1 t.1.mem m).prom
      (t.1.mem.append m).1 ((Q.P w).cov 1) := Inv2Rely.CohCoversL.promise h.core.cov1 m
  have hpr : ∀ k ∈ (Live.Sem.promThread t1 t.1.mem m).prom, (Q.SR w).T < k ∧
      ∃ w', (t.1.mem.append m).1.get? k = some w' ∧ w'.tid = 1 := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · obtain ⟨hTk, w', hg', ht'⟩ := h.core.prom1 k hk
      exact ⟨hTk, w', by rw [Scc.Sem.Memory.get?_append_le (Scc.Sem.Memory.le_last_of_get? hg')]; exact hg', ht'⟩
    · rw [List.mem_singleton.mp hk]
      exact ⟨Nat.lt_succ_of_le h.core.T_le, m, Scc.Sem.Memory.get?_append_new, hwt⟩
  have hnp : (Q.P w).noProm (Live.Sem.promThread t1 t.1.mem m).st → (Live.Sem.promThread t1 t.1.mem m).prom = [] :=
    fun hn => hC.noProm w _ _ _ hn hc
  have hfresh : t.1.mem.last + 1 ∉ t1.prom := fun hm' => by
    have h1 : @LE.le Nat instLENat (t.1.mem.last + 1) t.1.mem.last := hpl _ hm'
    omega
  have hnd : (Live.Sem.promThread t1 t.1.mem m).prom.Nodup :=
    List.nodup_append.mpr ⟨h.nodup, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, fun a ha b hb' => by
      rw [List.mem_singleton.mp hb']; rintro rfl; exact hfresh ha⟩
  by_cases hL : m.loc = (Q.C w).cT
  · -- at `cT`: the worker's `1` before its store, no `c` message yet
    have hv : m.val = 1 := hv1 hL
    -- the count: the new promise is of `cT`
    have hnewT : ((t.1.mem.append m).1.get? (t.1.mem.last + 1)).map Msg.loc = some (Q.C w).cT := by
      rw [Scc.Sem.Memory.get?_append_new]; simp [hL]
    have hcntE : cntT (Q.C w).cT (Live.Sem.promThread t1 t.1.mem m, (t.1.mem.append m).1) =
        t1.prom.countP (fun p => decide (((t.1.mem.append m).1.get? p).map Msg.loc = some (Q.C w).cT)) + 1 := by
      unfold cntT
      show List.countP _ (t1.prom ++ [t.1.mem.last + 1]) = _
      have hdec : decide (((t.1.mem.append m).1.get? (t.1.mem.last + 1)).map Msg.loc = some (Q.C w).cT) = true :=
        decide_eq_true hnewT
      rw [List.countP_append]
      simp only [List.countP_cons, List.countP_nil, hdec, ite_true]
    have hnpT : ¬ (Q.C w).passT t1.st := fun hp => by
      have h0 : passB Q w (Live.Sem.promThread t1 t.1.mem m, (t.1.mem.append m).1) = 0 := by
        unfold passB; exact ite_eq_left hp
      omega
    have hoc : oc = none := by
      cases oc with
      | none => rfl
      | some pr =>
        exfalso
        obtain ⟨Tc, kc⟩ := pr
        have hTp := hT0.prom_worker Tc kc rfl (hT0.pass_prom hnpT Tc kc rfl)
        obtain ⟨-, -, w', hg', hl', -⟩ := hT0.some_msg Tc kc rfl
        have hpos : 0 < t1.prom.countP
            (fun p => decide (((t.1.mem.append m).1.get? p).map Msg.loc = some (Q.C w).cT)) :=
          List.countP_pos_iff.mpr ⟨Tc, hTp, by simp [Scc.Sem.Memory.get?_append_le (hpl Tc hTp), hg', hl']⟩
        have h1 : passB Q w (Live.Sem.promThread t1 t.1.mem m, (t.1.mem.append m).1) ≤ 1 := by
          unfold passB; split <;> omega
        omega
    subst hoc
    have hs1p : s1.promises = [] := by
      cases hp : s1.promises with
      | nil => rfl
      | cons k ks =>
        obtain ⟨Tc, hTc⟩ := h.src_prom hC (show k ∈ s1.promises by rw [hp]; exact List.mem_cons_self)
        cases hTc
    obtain ⟨a', hcT, hcTa, hcTo⟩ := hC.cT w
    have hm : m = ⟨wordLoc a', 1, 1⟩ := by
      obtain ⟨L, V, tid⟩ := m
      simp only at hL hv hwt
      rw [hL, hcT, hv, hwt]
    subst hm
    -- the source worker's promise of `kc`
    obtain ⟨hT0', hS, hlink⟩ := (cProt_iff _ _ _).mp h.prot
    have hnpS : ¬ (Q.C w).passS s1 := fun hp => hnpT (hlink.mpr hp)
    have hlt := hS.pre_lt hnpS
    rw [hC.C w] at hlt
    have hSle : (Q.SR w).S ≤ s.mem.size := h.core.S_le
    have hSpos := hC.Spos w
    let s1' : TermRun.TTh := { s1 with promises := s1.promises ++ [s.mem.size] }
    obtain ⟨hg1, hgm⟩ := promise_get h.s1_get (Q.C w).cS (.num 1) ((Q.SR w).S - 1)
    have hnpre : s1.term ≠ wkUnpark ∧ s1.term ≠ .ret .unit := by
      have := (not_congr (hC.pass w _ _ h.pt1.1)).mp hnpT
      exact ⟨fun e => this (.inl e), fun e => this (.inr e)⟩
    have hcert := certified_pre (k := (srcPo 2 arch wakeSrc).k) (arch := (srcPo 2 arch wakeSrc).arch)
      (w := (Q.SR w).S - 1) hg1 h.wCtl hnpre hstk h.pt1.2.2.1 (hC.cwv w) (by simp [hs1p])
      (by rw [hgm]; simp) (Nat.le_pred_of_lt hlt.1) (Nat.lt_of_lt_of_le hlt.2 hSle)
    have hstep := prom_c_src (P := srcPo 2 arch wakeSrc) (p := wakeSrc) rfl
      (by rw [h.ths]; simp) (by omega) hcert hex
    have hrun : (wakeS arch).Run s [] (TermRun.promise s 1 (Q.C w).cS (.num 1) ((Q.SR w).S - 1)) :=
      LRun.step (step := fun c es c' => ∃ i, (wakeS arch).step i c es c') ⟨1, hstep⟩ (LRun.refl _)
    have hs' : (TermRun.promise s 1 (Q.C w).cS (.num 1) ((Q.SR w).S - 1)).ths = #[s0, s1'] := by
      unfold TermRun.promise; rw [h.s1_get]; show s.ths.set! 1 s1' = _; rw [h.ths]; rfl
    -- the memory relation: `Tc ↦ kc`, both mirrored
    have hvr : ValRep (Q.SR w).lbl (WeakMem.Val.num 1) (BitVec.toNat (1 : Val)) := ⟨by decide, rfl⟩
    have hmem := h.core.mem.store (a := a') (v := 1) (tid := 1)
      (m := ⟨(Q.C w).cS, .num 1, (Q.SR w).S - 1⟩) hcTa hcTo hvr true
    have hcore := core1_append h.core
      (own' := fun i => if i = 0 then Q.own w 0 t0.st s0.stack
        else Q.own w 1 (Live.Sem.promThread t1 t.1.mem ⟨wordLoc a', 1, 1⟩).st s1'.stack)
      (w := ⟨wordLoc a', 1, 1⟩) (t1' := Live.Sem.promThread t1 t.1.mem ⟨wordLoc a', 1, 1⟩)
      (sm' := s.mem.push ⟨(Q.C w).cS, .num 1, (Q.SR w).S - 1⟩) (s1' := s1')
      (ts' := fun k => if k = s.mem.size then some (t.1.mem.last + 1) else ts k)
      (tp' := tp ++ [t.1.mem.last + 1]) (sp' := sp ++ [s.mem.size])
      (by simp) rfl hf (.inr ⟨_, rfl⟩) hmem
      (fun k hk => by
        rcases List.mem_append.mp hk with hk | hk
        · rcases h.core.tp_prom k hk with h0 | h1
          · exact .inl h0
          · exact .inr (List.mem_append_left _ h1)
        · exact .inr (List.mem_append_right _ hk))
      (fun k w' hk hg' hin' => by
        rcases hk with hk0 | hk1
        · obtain ⟨-, w0, hg0, -⟩ := h.core.prom0 k hk0
          rw [Scc.Sem.Memory.get?_append_le (Scc.Sem.Memory.le_last_of_get? hg0)] at hg'
          exact List.mem_append_left _ (h.core.prom_tp k w' (.inl hk0) hg' hin')
        · rcases List.mem_append.mp hk1 with hk1 | hk1
          · rw [Scc.Sem.Memory.get?_append_le (hpl k hk1)] at hg'
            exact List.mem_append_left _ (h.core.prom_tp k w' (.inr hk1) hg' hin')
          · exact List.mem_append_right _ hk1)
      (fun k => by
        show k ∈ sp ++ [s.mem.size] ↔ k ∈ s0.promises ∨ k ∈ s1.promises ++ [s.mem.size]
        rw [List.mem_append, List.mem_append, h.core.sp_prom k, or_assoc])
      rfl hin hfit hG hb hcov
      (Inv2Rely.frzS_push h.core.frzS (hC.cSfrz w)) (Inv2Rely.scov_push h.core.scov0 (hC.cSfrz w))
      (Inv2Rely.scov_push h.core.scov1 (hC.cSfrz w)) hown' hdisj hocov hpr hnp
    -- the protocol at `oc = (Tc, kc)`
    have hT' : CProtT (Q.SR w) (Q.C w) (some (t.1.mem.last + 1, s.mem.size)) (t.1.mem.append ⟨wordLoc a', 1, 1⟩).1
        (Live.Sem.promThread t1 t.1.mem ⟨wordLoc a', 1, 1⟩)
        (fun k => if k = s.mem.size then some (t.1.mem.last + 1) else ts k) (tp ++ [t.1.mem.last + 1]) :=
      { tmsg := fun k w' hk hTk hl => by
          by_cases hk' : k = t.1.mem.last + 1
          · subst hk'
            rw [Scc.Sem.Memory.get?_append_new] at hk
            cases hk
            exact ⟨_, rfl, rfl⟩
          · obtain ⟨kc, hoc', -⟩ := hT0.tmsg k w' (CohCoversP.get?_append_ne hk hk') hTk hl
            cases hoc'
        some_msg := fun Tc kc hoc' => by
          cases hoc'
          exact ⟨Nat.lt_succ_of_le h.core.T_le, by simp, _, Scc.Sem.Memory.get?_append_new, hcT.symm, rfl, rfl⟩
        prom_worker := fun Tc kc hoc' _ => by
          cases hoc'; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
        pass_done := fun hp => absurd hp hnpT
        pass_prom := fun _ Tc kc hoc' => by
          cases hoc'; exact List.mem_append_right _ (List.mem_singleton.mpr rfl) }
    have hS' := cProtS_prom (Tc := t.1.mem.last + 1) (tp' := tp ++ [t.1.mem.last + 1]) (sp' := sp ++ [s.mem.size])
      hS hSle hSpos (by rw [hC.C w]; exact helloC_vs.1) (by rw [hC.C w]; exact helloC_vs.2)
    have hpt1 : PT1 D w (t.1.mem.append ⟨wordLoc a', 1, 1⟩).1 (s.mem.push ⟨(Q.C w).cS, .num 1, (Q.SR w).S - 1⟩)
        (Live.Sem.promThread t1 t.1.mem ⟨wordLoc a', 1, 1⟩) s1' :=
      ⟨h.pt1.1, hstk, h.pt1.2.2.1, h.pt1.2.2.2.1, h.pt1.2.2.2.2.1, h.pt1.2.2.2.2.2.1, by simp [s1', hs1p],
        fun k hk => by
          have hk' : k = s.mem.size := by simpa [s1', hs1p] using hk
          subst hk'
          exact ⟨by rw [hC.S w]; exact hSle, ⟨(Q.C w).cS, .num 1, (Q.SR w).S - 1⟩, by simp, hC.cwv w⟩, hnd⟩
    refine ⟨_, hrun, post_frame (ts' := fun k => if k = s.mem.size then some (t.1.mem.last + 1) else ts k)
      (tp' := tp ++ [t.1.mem.last + 1]) (sp' := sp ++ [s.mem.size])
      hC h.th h.ths hs' h.preC h.pt0 h.kr h.core.T_le ?_ ?_ ?_ ?_ (by unfold TermRun.promise; split <;> rfl)⟩
    · rw [hgm]; exact ⟨.inr ⟨_, rfl, rfl, hf⟩, .inr ⟨_, rfl, rfl⟩⟩
    · rw [hgm]; exact hcore
    · rw [hgm]; exact hpt1
    · rw [hgm]
      exact ⟨_, (cProt_iff _ _ _).mpr ⟨hT', hS', ⟨fun hp => absurd hp hnpT,
        fun hp => absurd ((Parts.passS_iff hC s1).mpr ((Parts.passS_iff hC s1').mp hp)) hnpS⟩⟩⟩
  · -- off `cT`: out of every placed label, the source stutters
    have hout : ¬ InLabel (Q.SR w).lbl (Q.SR w).lsize m.loc := fun hi => hL (hC.footLab w _ hf hi)
    have hT' : CProtT (Q.SR w) (Q.C w) oc (t.1.mem.append m).1 t1 ts tp :=
      { hT0 with
        tmsg := fun k w' hk hTk hl => by
          by_cases hk' : k = t.1.mem.last + 1
          · subst hk'
            rw [Scc.Sem.Memory.get?_append_new] at hk
            cases hk
            exact absurd hl hL
          · exact hT0.tmsg k w' (CohCoversP.get?_append_ne hk hk') hTk hl
        some_msg := fun Tc kc hoc => by
          obtain ⟨h1, h2, w', hg', h3⟩ := hT0.some_msg Tc kc hoc
          exact ⟨h1, h2, w', by rw [Scc.Sem.Memory.get?_append_le (Scc.Sem.Memory.le_last_of_get? hg')]; exact hg',
            h3⟩ }
    have hcore := core1_append h.core
      (own' := fun i => if i = 0 then Q.own w 0 t0.st s0.stack
        else Q.own w 1 (Live.Sem.promThread t1 t.1.mem m).st s1.stack)
      (w := m) (t1' := Live.Sem.promThread t1 t.1.mem m) (sm' := s.mem) (s1' := s1) (ts' := ts) (tp' := tp)
      (sp' := sp) (by simp) hwt hf (.inl rfl) (h.core.mem.runtime_write hout)
      (fun k hk => by
        rcases h.core.tp_prom k hk with h0 | h1
        · exact .inl h0
        · exact .inr (List.mem_append_left _ h1))
      (fun k w' hk hg' hin' => by
        rcases hk with hk0 | hk1
        · obtain ⟨-, w0, hg0, -⟩ := h.core.prom0 k hk0
          rw [Scc.Sem.Memory.get?_append_le (Scc.Sem.Memory.le_last_of_get? hg0)] at hg'
          exact h.core.prom_tp k w' (.inl hk0) hg' hin'
        · rcases List.mem_append.mp hk1 with hk1 | hk1
          · rw [Scc.Sem.Memory.get?_append_le (hpl k hk1)] at hg'
            exact h.core.prom_tp k w' (.inr hk1) hg' hin'
          · rw [List.mem_singleton.mp hk1, hnew, Scc.Sem.Memory.get?_append_new] at hg'
            cases hg'
            exact absurd hin' hout)
      h.core.sp_prom hb8 hin hfit hG hb hcov h.core.frzS h.core.scov0 h.core.scov1 hown' hdisj hocov hpr hnp
    exact post_local hC h hex (.inr ⟨m, rfl, hwt, hf⟩) hcore hT'
      (fun Tc kc hoc htp => List.mem_append_left _ (hT0.prom_worker Tc kc hoc htp)) (fun k hk => hk) hnd
      (LocalRun.refl _) h.pt1.1

/-- info: 'Spike.Lib.WakeW1.cstep_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cstep_shape

/-- info: 'Spike.Lib.WakeW1.cstep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cstep

/-- info: 'Spike.Lib.WakeW1.post_prom1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_prom1

end Spike.Lib.WakeW1

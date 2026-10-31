/-
**main's certified promises** (`post_step0`).
The thread-0 counterpart of `Spike/Lib/WakeW1Prom.lean`, simpler: main
never writes the flag, so there is no potential.

A promise of main is certified by a run of main alone under the
certification semantics. From main's invariant (`CInv0`: a pair of `Mi`
with the control invariant, the `G` values of the messages not promised)
every step of that run is one of main's rows (`MSide.closed`): it keeps
memory and promises, or writes a `Good0` message (in main's footprint, in a
shared region, a `G` value, one word wide, out of every placed label:
`WCompat0.mpW0`). At the flag load the run continues by `WCompat0.flagLd`
(the value `1` bound to a word `rd` reads, `WCompat0.rd1`). So every promise the run
fulfils is `Good0` (`prom_good0`), and a certified promise of main is out of
every placed label: the source stutters (`post_prom0`).

- `CInv0`, `Good0`: the certification run's invariant, a message main may
  write.
- `flagLd_step`: a certification step at main's flag load.
- `cstep0_shape`, `cstep0`: one certification step from `CInv0`.
- `prom_good0`: a certified promise of main is `Good0`.
- `post_prom0`: main's promise row keeps `Post`.
-/
import Spike.Lib.WakeM0Rt
import Spike.Lib.WakeM0Rows
import Spike.Lib.WakeW1Prom

namespace Spike.Lib.WakeM0

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt Spike.Lib.WakeW1
open Spike.Lib.WakeMLive (wlRet)

/-! ## The certification run's invariant -/

/-- **A silent row** (`Out.silent`, `Out.choice`) at any thread: memory and
promises kept, the state a leaf (`WakeW1.stepOne_silent_keep` at any
thread). -/
theorem stepOne_silent_keep' (tid : Nat) {t : Thread isaLSE2} {mem : Memory} {tree : EvTree isaLSE2.State}
    {P : isaLSE2.State → Prop} (hex : isaLSE2.exec t.st = some tree) (hs : Lower.SilentTree P tree)
    {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2}
    (hso : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok o ∈ outs) :
    o.mem = mem ∧ o.thread.prom = t.prom ∧ P o.thread.st := by
  obtain ⟨st, hP, hth, hm⟩ := Lower.stepOne_silent_ok Arch.armv8 tid hex hs ⟨outs, o, hso, ho, rfl, rfl⟩
  exact ⟨hm, (finishInstr_relKey hth).1, (finishInstr_st hth) ▸ hP⟩

/-- **main's certification run's invariant** at the ghost record `w`: main's
state paired with a control in `Mi` under the control invariant, the
messages not promised and the initial values `G` values, the promises in
memory. -/
structure CInv0 (Q : WakeRel) (M : MSide Q.ι) (w : Q.ι) (x : Thread isaLSE2 × Memory) : Prop where
  mi : ∃ c, M.Mi w x.1.st c ∧ MCtl (M.cw w) c
  msgs : MsgsExcept (fun m => Q.G w m.loc m.val) x.1.prom x.2
  init : ∀ l, Q.G w l (x.2.initVal l)
  le : ∀ p ∈ x.1.prom, p ≤ x.2.last

/-- **A message main may write**: in its footprint, in a shared region, a
`G` value, one word wide, of a 64-bit value, out of every placed label. -/
def Good0 (Q : WakeRel) (Λ : Scc.Sem.Layout) (w : Q.ι) (m : Msg) : Prop :=
  (Q.P w).foot 0 m.loc ∧ Consumer1.LocIn Λ.shared m.loc ∧ Q.G w m.loc m.val ∧ m.loc.bytes = 8 ∧
    m.val.toNat < 2 ^ 64 ∧ ¬ InLabel (Q.SR w).lbl (Q.SR w).lsize m.loc

variable {Q : WakeRel} {D : WSide Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch} {w : Q.ι}

/-- **A step at main's flag load** (`WCompat0.flagLd`): memory and promises
kept, and the new state paired in `Mi` with a control under the control
invariant (stuttering, or past the load with `d` bound to a word of `1`). -/
theorem flagLd_step (hC0 : WCompat0 Q M μ Λ)
    {c : Ctl} {st : isaLSE2.State}
    (hmi : M.Mi w st c) (hc : MCtl (M.cw w) c) (ht : c.term = wlBody) {kl : Kraken.LoadKind} {A : BitVec 64}
    {g : Val → isaLSE2.State} (he : isaLSE2.exec st = some (.load kl false ⟨A, 8⟩ fun v => .done (g v)))
    {ty : Ty} {wd : TermRun.Word} (hev : TermRun.evalAt c.env (.var "c") = some (ty, [wd]))
    (hv : ValRep (M.lbl w) wd.val A.toNat) (v : Val) :
    ∃ c', M.Mi w (g v) c' ∧ MCtl (M.cw w) c' := by
  obtain ⟨hne, heq⟩ := hC0.flagLd w st c kl A g ty wd hmi ht he hev hv
  by_cases h1 : (v.setWidth 64).toNat = 1
  · let one' : TermRun.Word := TermRun.cst (.num 1)
    refine ⟨_, heq v one' h1 (hC0.rd1 w one' rfl) ⟨by decide, rfl⟩, rfl, .inr (.inr (.inl rfl)), ?_⟩
    exact envC_cons hc.env (by decide) _ _
  · exact ⟨c, hne v h1, hc⟩

/-- **One certification step of main from `CInv0`, by the rows**: to a
control `c'` in `Mi` under the control invariant, it keeps memory and
promises, or writes a `Good0` message (appended, or fulfilling a promise of
it). -/
theorem cstep0_shape (hC0 : WCompat0 Q M μ Λ)
    {k : KState} {x y : Thread isaLSE2 × Memory}
    (hq : CInv0 Q M w x) (hs : ThreadStepC Arch.armv8 (certSem abi Arch.armv8 μ k 0) 0 x y) :
    ∃ c', M.Mi w y.1.st c' ∧ MCtl (M.cw w) c' ∧
      ((y.2 = x.2 ∧ y.1.prom = x.1.prom) ∨
       ∃ L V, Good0 Q Λ w ⟨L, V, 0⟩ ∧
         ((y.2 = (x.2.append ⟨L, V, 0⟩).1 ∧ y.1.prom = x.1.prom) ∨
          (∃ q ∈ x.1.prom, x.2.get? q = some ⟨L, V, 0⟩ ∧ y.2 = x.2 ∧ y.1.prom = x.1.prom.erase q))) := by
  obtain ⟨c, hmi, hctl⟩ := hq.mi
  obtain ⟨outs, o, hso, ho, rfl⟩ := hs
  have hsite := hC0.noSite0 w _ _ hmi
  have hown : ∀ s, (M.ms w).own s = [] := hC0.own0 w
  have hmpG : ∀ a V, (M.ms w).mp (wordLoc a) true → Q.G w (wordLoc a) V → V.toNat < 2 ^ 64 →
      Good0 Q Λ w ⟨wordLoc a, V, 0⟩ := by
    intro a V hmp hG hf
    obtain ⟨hf1, hout, hin⟩ := hC0.mpW0 w _ hmp
    exact ⟨hf1, hin, hG, rfl, hf, hout⟩
  have hkeep : ∀ {c'}, LocalRun wakeSrc c c' → M.Mi w o.thread.st c' → o.mem = x.2 → o.thread.prom = x.1.prom →
      ∃ c', M.Mi w (o.thread, o.mem).1.st c' ∧ MCtl (M.cw w) c' ∧
        (((o.thread, o.mem).2 = x.2 ∧ (o.thread, o.mem).1.prom = x.1.prom) ∨
         ∃ L V, Good0 Q Λ w ⟨L, V, 0⟩ ∧
           (((o.thread, o.mem).2 = (x.2.append ⟨L, V, 0⟩).1 ∧ (o.thread, o.mem).1.prom = x.1.prom) ∨
            (∃ q ∈ x.1.prom, x.2.get? q = some ⟨L, V, 0⟩ ∧ (o.thread, o.mem).2 = x.2 ∧
              (o.thread, o.mem).1.prom = x.1.prom.erase q))) :=
    fun hr hX hm hp => ⟨_, hX, localRun_mCtl hr hctl, .inl ⟨hm, hp⟩⟩
  -- the flag load (an `Out.load` or `OutL.ldSt` row, at `wlBody` by `mterm_load`)
  have hflag : ∀ {kl : Kraken.LoadKind} {A : BitVec 64} {g : Val → isaLSE2.State} {x' : String} {a : At}
      {e : Expr} {ty : Ty} {wd : TermRun.Word},
      isaLSE2.exec x.1.st = some (.load kl false ⟨A, 8⟩ fun v => .done (g v)) →
      c.term = .let_ x' (.load true a) e → TermRun.evalAt c.env a = some (ty, [wd]) →
      ValRep (M.lbl w) wd.val A.toNat →
      ∃ c', M.Mi w (o.thread, o.mem).1.st c' ∧ MCtl (M.cw w) c' ∧
        (((o.thread, o.mem).2 = x.2 ∧ (o.thread, o.mem).1.prom = x.1.prom) ∨
         ∃ L V, Good0 Q Λ w ⟨L, V, 0⟩ ∧
           (((o.thread, o.mem).2 = (x.2.append ⟨L, V, 0⟩).1 ∧ (o.thread, o.mem).1.prom = x.1.prom) ∨
            (∃ q ∈ x.1.prom, x.2.get? q = some ⟨L, V, 0⟩ ∧ (o.thread, o.mem).2 = x.2 ∧
              (o.thread, o.mem).1.prom = x.1.prom.erase q))) := by
    intro kl A g x' a e ty wd he ht hev hv
    obtain ⟨hb, -, -, ha, -⟩ := mterm_load hctl.term ht
    subst ha
    have he0 : isaLSE2.exec x.1.st = some (.load kl false ⟨A, 8⟩ fun v => .done (g v)) := he
    rw [certSem_step_of_not_site hsite (by
      cases hat : abi.atSys x.1.st
      · rfl
      · obtain ⟨m, hm⟩ := hC0.sysExec0 w _ _ _ hmi hat he0; cases hm)] at hso
    obtain ⟨hm, hp⟩ := stepOne_load_keep' 0 he0 hso ho
    obtain ⟨v, hst, -⟩ := stepOne_load_msgsExcept (G := Q.G w) he0 hso ho hq.msgs hq.init
    obtain ⟨c', hX, hc'⟩ := flagLd_step hC0 hmi hctl hb he0 hev hv v
    exact ⟨c', hst ▸ hX, hc', .inl ⟨hm, hp⟩⟩
  cases hat : abi.atSys x.1.st
  · rw [certSem_step_of_not_site hsite hat] at hso
    cases M.closed w _ _ hmi with
    | out r =>
      cases r with
      | silent s' c' he hr hX =>
        obtain ⟨hm, hp, hst⟩ := stepOne_silent_keep' 0 he (Lower.silentTree_done s') hso ho
        exact hkeep hr (hst ▸ hX) hm hp
      | choice P tree he hsil hX =>
        obtain ⟨hm, hp, hP⟩ := stepOne_silent_keep' 0 he hsil hso ho
        obtain ⟨c', hr, hX'⟩ := hX _ hP
        exact hkeep hr hX' hm hp
      | load kl A g x' a e ty wd he ht hev hv => exact hflag he ht hev hv
      | store kr A V s' x' a b e ty tb wa wb he ht => exact (mterm_not_store hctl.term ht).elim
      | rtStore kr L V s' c' he hrt hmp hG hr hX =>
        have hwide := hC0.wide0 w _ _ hmi
        have hL8 : L.bytes = 8 := (Scc.Cert.WideA64.execLSE2_w8 hwide he).1
        have hfit : V.toNat < 2 ^ 64 := (Scc.Cert.WideA64.execLSE2_fit hwide he).1
        rw [hC0.G0 w] at hG
        obtain ⟨a, rfl⟩ : ∃ a, L = wordLoc a := ⟨_, ExtRows.loc_wordLoc hL8⟩
        obtain ⟨hst, hc⟩ := stepOne_store_cases Arch.armv8 he hso ho hq.le
        refine ⟨c', hst ▸ hX, localRun_mCtl hr hctl, .inr ⟨wordLoc a, V, hmpG a V hmp hG hfit, ?_⟩⟩
        rcases hc with ⟨q, hq', hg, -, hm, hp⟩ | ⟨hm, hp⟩
        · exact .inr ⟨q, hq', hg, hm, hp⟩
        · exact .inl ⟨hm, hp⟩
      | rtLoad kl L g c' he hrt hmp hr hX =>
        obtain ⟨hm, hp⟩ := stepOne_load_keep' 0 he hso ho
        obtain ⟨v, hst, hG⟩ := stepOne_load_msgsExcept (G := Q.G w) he hso ho hq.msgs hq.init
        rw [← hC0.G0 w] at hG
        refine hkeep hr ?_ hm hp
        rw [hst]; exact hX v hG fun u hu => by simp [hown] at hu
      | rtRmw k' L op g c' he hrt hmp hr hX =>
        have hwide := hC0.wide0 w _ _ hmi
        have hL8 : L.bytes = 8 := (Scc.Cert.WideA64.execLSE2_w8 hwide he).1
        have hfit : ∀ old v, op old = some v → v.toNat < 2 ^ 64 := (Scc.Cert.WideA64.execLSE2_fit hwide he).1
        obtain ⟨a, rfl⟩ : ∃ a, L = wordLoc a := ⟨_, ExtRows.loc_wordLoc hL8⟩
        obtain ⟨old, tr, hst, hrd, hn, hc⟩ := stepOne_rmw_casesG Arch.armv8 he hso ho hq.le
        have hGo := msgsExcept_read (G := Q.G w) hq.msgs hq.init hrd hn
        rw [← hC0.G0 w] at hGo
        obtain ⟨hGn, hXo⟩ := hX old hGo (fun u hu => by simp [hown] at hu)
        rcases hc with ⟨-, hm, hp⟩ | ⟨new, hop, hc⟩
        · exact hkeep hr (hst ▸ hXo) hm hp
        · have hGn' := hGn new hop
          rw [hC0.G0 w] at hGn'
          refine ⟨c', hst ▸ hXo, localRun_mCtl hr hctl,
            .inr ⟨wordLoc a, new, hmpG a new hmp hGn' (hfit old new hop), ?_⟩⟩
          rcases hc with ⟨q, hq', hg, hm, hp⟩ | ⟨hm, hp⟩
          · exact .inr ⟨q, hq', hg, hm, hp⟩
          · exact .inl ⟨hm, hp⟩
      | sys K call hK ha =>
        rw [hC0.K0 w] at hK; cases hK; rw [hat] at ha; cases ha
      | holdLoad kl A g x' sa u v e he hxs => exact (mterm_not_xchgSite hctl.term hxs).elim
      | xchgStore kr A V s' x' sa u v e tv wv wold he hxs hA hh =>
        rw [hctl.hold] at hh; cases hh
      | ctrRmw k' op g x' τ e n he hrt hm hs =>
        rcases hs with ⟨a, -, -, ht, -⟩ | ⟨-, a, -, ⟨_, ht⟩, -⟩
        · exact (mterm_not_newBuf hctl.term ht).elim
        · rcases mterm_let hctl.term ht with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> cases h
      | alloc s' A x' a τ e ta ws k' wold old us he ht => exact (mterm_not_newBuf hctl.term ht).elim
      | newStore kr A V s' x' a t e w' wold old _ he hm ht =>
        obtain ⟨_, ht⟩ := ht
        rcases mterm_let hctl.term ht with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> cases h
      | emit K buf n Pw Qw hK ha =>
        rw [hC0.K0 w] at hK; cases hK; rw [hat] at ha; cases ha
      | fence k' s' c' he hr hX =>
        obtain ⟨hst, hm, hp⟩ := stepOne_fence_eq Arch.armv8 he hso ho
        cases hr with
        | loc hr => exact hkeep hr (hst ▸ hX) hm hp
        | pub _ hps _ =>
          -- main's terms publish nothing
          obtain ⟨-, -, x', a, e, t, t', ws, hpt, -⟩ := hps
          rcases hpt with ⟨ht, -⟩ | ⟨r, ht, -⟩ <;>
            rcases mterm_let hctl.term ht with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> cases h
    | ldSt kl A g x' a e ty wd V he ht hev hv => exact hflag he ht hev hv
  · cases M.closed w _ _ hmi with
    | out r =>
      cases r with
      | sys K call hK ha hd hok hX =>
        rw [hC0.K0 w] at hK; cases hK
        obtain ⟨hm, hp, hmem⟩ := certSem_step_sys hsite ha hd hok.2.1 hso ho
        obtain ⟨c', hr, hX'⟩ := hX _ hmem
        exact hkeep hr hX' hm hp
      | emit K buf n Pw Qw hK ha hd =>
        rw [hC0.K0 w] at hK; cases hK
        exact absurd hd (hC0.noWrite0 w _ _ 1 buf n hmi ha)
      | choice P tree he hsil hX =>
        obtain ⟨m, rfl⟩ := hC0.sysExec0 w _ _ _ hmi hat he
        cases hsil
      | _ =>
        obtain ⟨m, hm⟩ := hC0.sysExec0 w _ _ _ hmi hat ‹isaLSE2.exec x.1.st = some _›
        cases hm
    | ldSt _ _ _ _ _ _ _ _ _ he =>
      obtain ⟨m, hm⟩ := hC0.sysExec0 w _ _ _ hmi hat he
      cases hm

/-- **One certification step of main from `CInv0`**: it lands in `CInv0`
and every promise it fulfils is of a `Good0` message. -/
theorem cstep0 (hC0 : WCompat0 Q M μ Λ)
    {k : KState} {x y : Thread isaLSE2 × Memory}
    (hq : CInv0 Q M w x) (hs : ThreadStepC Arch.armv8 (certSem abi Arch.armv8 μ k 0) 0 x y) :
    CInv0 Q M w y ∧ (∀ p ∈ x.1.prom, p ∉ y.1.prom → ∀ m, x.2.get? p = some m → Good0 Q Λ w m) := by
  obtain ⟨c', hmi', hctl', hcase⟩ := cstep0_shape (Λ := Λ) hC0 hq hs
  rcases hcase with ⟨hm, hp⟩ | ⟨L, V, hg, ⟨hm, hp⟩ | ⟨q, hqp, hgq, hm, hp⟩⟩
  · exact ⟨⟨⟨c', hmi', hctl'⟩, msgsExcept_of_eq hq.msgs hm hp, by rw [hm]; exact hq.init,
      by rw [hm, hp]; exact hq.le⟩, fun p hp1 hp2 => absurd (hp ▸ hp1) hp2⟩
  · refine ⟨⟨⟨c', hmi', hctl'⟩, hm ▸ hp ▸ msgsExcept_append hq.msgs hg.2.2.1,
      fun l => by rw [hm, (Memory.Prefix.append _ _).initVal]; exact hq.init l,
      fun p hp1 => ?_⟩, fun p hp1 hp2 => absurd (hp ▸ hp1) hp2⟩
    rw [hp] at hp1; rw [hm, Memory.last_append]; exact Nat.le_succ_of_le (hq.le p hp1)
  · refine ⟨⟨⟨c', hmi', hctl'⟩, hm ▸ hp ▸ msgsExcept_erase hq.msgs hgq hg.2.2.1,
      by rw [hm]; exact hq.init, fun p hp1 => by rw [hp] at hp1; rw [hm]; exact hq.le p (List.mem_of_mem_erase hp1)⟩,
      fun p hp1 hp2 m hgm => ?_⟩
    have hpq : p = q := Classical.byContradiction fun hpq =>
      hp2 (by rw [hp]; exact (List.mem_erase_of_ne hpq).mpr hp1)
    subst hpq; rw [hgq] at hgm; cases hgm; exact hg

/-! ## The promise row -/

variable {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **A certified promise of main is `Good0`**: from `CInv0` at the
promising configuration, `cstep0` gives `StepG` (`certOkC_prom_good_cfg`). -/
theorem prom_good0 (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hmi : M.Mi w t0.st (Ctl.of s0)) {m : Msg}
    (hc : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 0) 0 (Live.Sem.promThread t0 t.1.mem m)
      (t.1.mem.append m).1) :
    Good0 Q Λ w m := by
  have hq : CInv0 Q M w (Live.Sem.promThread t0 t.1.mem m, (t.1.mem.append m).1) :=
    { mi := ⟨Ctl.of s0, hmi, h.mCtl hPT0⟩
      msgs := msgsExcept_promise (Scc.Sem.MemInv.msgsExcept h.core.memInv _) m
      init := fun l => by
        show Q.G w l ((t.1.mem.append m).1.initVal l)
        rw [(Memory.Prefix.append _ _).initVal]; exact h.core.memInv.1 l
      le := fun p hp => by
        show p ≤ (t.1.mem.append m).1.last
        rw [Memory.last_append]
        rcases List.mem_append.mp hp with hp | hp
        · exact Nat.le_succ_of_le (h.prom_le0 p hp)
        · rw [List.mem_singleton.mp hp]; exact Nat.le_refl _ }
  have hG : StepG Arch.armv8 (certSem abi Arch.armv8 μ t.2 0) 0 (CInv0 Q M w) (Good0 Q Λ w) :=
    fun x y hx' hs _ => cstep0 hC0 hx' hs
  exact certOkC_prom_good_cfg hG hq hc (p := t.1.mem.last + 1) (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    (Scc.Sem.Memory.get?_append_new)

/-- **main's certified promise keeps `Post`**: the promised message is
`Good0` (`prom_good0`), out of every placed label, so off `cT`; the source
stutters (`post_local0`). -/
theorem post_prom0 (hC : WCompat Q D μ Λ arch) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = WakeKR.KR r0 r1) (hown : Q.own = WakeOwn.wakeOwn) (hwf : Λ.WF)
    (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hx : t.2.exited = none) {m : Msg} (hwt : m.tid = 0)
    (hc : CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 0) 0 (Live.Sem.promThread t0 t.1.mem m)
      (t.1.mem.append m).1) :
    ∃ s', (wakeS arch).Run s [] s' ∧
      Q.Post Λ (t.1.withThread 0 (Live.Sem.promThread t0 t.1.mem m) (t.1.mem.append m).1, t.2) s' := by
  have hmi := h.mi0 hPT0 hKR hx
  obtain ⟨hf, hin, hG, hb8, hfit, hout⟩ := prom_good0 hC0 hPT0 h hmi hc
  have hpl := h.prom_le0
  have hlast : (t.1.mem.append m).1.last = t.1.mem.last + 1 := Memory.last_append _ _
  have hnew : (t.1.mem.append m).2 = t.1.mem.last + 1 := rfl
  have hcTin : InLabel (Q.SR w).lbl (Q.SR w).lsize (Q.C w).cT := by
    obtain ⟨a', hcT, hx, ho⟩ := hC.cT w
    rw [hcT]; exact inLabel_wordLoc h.core.mem hwf hx ho
  have hne : m.loc ≠ (Q.C w).cT := fun e => hout (e ▸ hcTin)
  have hb : (Live.Sem.promThread t0 t.1.mem m).Bnd (t.1.mem.append m).1.last := by
    have hle : t.1.mem.last ≤ (t.1.mem.append m).1.last := by rw [hlast]; exact Nat.le_succ _
    exact ⟨h.core.bnd0.views.mono hle, h.core.bnd0.regs.mono hle⟩
  have hcov : CohCoversL (Live.Sem.promThread t0 t.1.mem m).views (Live.Sem.promThread t0 t.1.mem m).prom
      (t.1.mem.append m).1 ((Q.P w).cov 0) := Inv2Rely.CohCoversL.promise h.core.cov0 m
  have hpr : ∀ k ∈ (Live.Sem.promThread t0 t.1.mem m).prom, (Q.SR w).T < k ∧
      ∃ w', (t.1.mem.append m).1.get? k = some w' ∧ w'.tid = 0 := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · obtain ⟨hTk, w', hg', ht'⟩ := h.core.prom0 k hk
      exact ⟨hTk, w', by rw [Scc.Sem.Memory.get?_append_le (Scc.Sem.Memory.le_last_of_get? hg')]; exact hg', ht'⟩
    · rw [List.mem_singleton.mp hk]
      exact ⟨Nat.lt_succ_of_le h.core.T_le, m, Scc.Sem.Memory.get?_append_new, hwt⟩
  have hnp : (Q.P w).noProm (Live.Sem.promThread t0 t.1.mem m).st → (Live.Sem.promThread t0 t.1.mem m).prom = [] :=
    fun hn => hC0.noProm0 w _ _ _ hn hc
  have hcore := core0_append h.core
    (own' := fun i => if i = 0 then Q.own w 0 (Live.Sem.promThread t0 t.1.mem m).st s0.stack
      else Q.own w 1 t1.st s1.stack)
    (w := m) (t0' := Live.Sem.promThread t0 t.1.mem m) (sm' := s.mem) (s0' := s0) (ts' := ts) (tp' := tp)
    (sp' := sp) (by simp) hwt hf (.inl rfl) (h.core.mem.runtime_write hout)
    (fun k hk => by
      rcases h.core.tp_prom k hk with h0 | h1
      · exact .inl (List.mem_append_left _ h0)
      · exact .inr h1)
    (fun k w' hk hg' hin' => by
      rcases hk with hk0 | hk1
      · rcases List.mem_append.mp hk0 with hk0 | hk0
        · rw [Scc.Sem.Memory.get?_append_le (hpl k hk0)] at hg'
          exact h.core.prom_tp k w' (.inl hk0) hg' hin'
        · rw [List.mem_singleton.mp hk0, hnew, Scc.Sem.Memory.get?_append_new] at hg'
          cases hg'
          exact absurd hin' hout
      · obtain ⟨-, w1, hg1, -⟩ := h.core.prom1 k hk1
        rw [Scc.Sem.Memory.get?_append_le (Scc.Sem.Memory.le_last_of_get? hg1)] at hg'
        exact h.core.prom_tp k w' (.inr hk1) hg' hin')
    h.core.sp_prom hb8 hin hfit hG hb hcov h.core.frzS h.core.scov0 h.core.scov1
    (fun L v h0 => by simp [hown, WakeOwn.wakeOwn] at h0) (fun L v v' h0 => by simp [hown, WakeOwn.wakeOwn] at h0)
    (fun L v h0 => by simp [hown, WakeOwn.wakeOwn] at h0) hpr hnp
  exact post_local0 hC hC0 hPT0 hKR h hcore (cProt_append0 h.prot hne) (h.preC.append h.core.T_le m)
    (LocalRun.refl _) hmi

/-- info: 'Spike.Lib.WakeM0.post_prom0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_prom0

end Spike.Lib.WakeM0

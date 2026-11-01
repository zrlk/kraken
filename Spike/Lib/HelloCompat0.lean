/-
**hello.w on AArch64: main's compatibility facts after the spawn**
(`WakeM0.WCompat0` at hello's relation; the twin of `WakeInst` /
`WakeInstFields`' `WCompat0` fields and `WakeAssemblyR.hC0R`): every field
of `WCompat0` at `HelloQ.helloQ` with main's side `HelloMainInv.helloM`,
generic in the records `ι`, main's memory side `ms` and the worker's side.

The fields read off main's invariant (`mainInvP helloSrc` inside
`mainWRH`): `live0H`, `wide0H`, `relW0H`, `sysExec0H` (the state's
executable, `[ValidLayout exe]`), `noWrite0H` (`MainSys`), `noSite0H` (from
`AbOffA` given `hns`, the labels off the marks' sites; at a placed output
`A64AbOffL.noSite_of_A_ofPlaceOK`) and `flagLdH` (`FlagW`, as
`WakeInst.flagLd_I`). `flagLdH` reads three facts of the memory side, named
premises in place of `WakeInst.wakeMs`' definitions: its kernel model
(`hK`), its runtime addresses off every placed label (`hrt`) and its read
side taking every number (`hrdN`).

`hC0H` assembles `WCompat0`; the memory side's remaining facts (`hlbl`,
`hG`, `hown`, `hmpW`, `habt`), main's pointer word (`hcw`) and the
certified no-promise fact (`hnp`) are its premises.
-/
import Spike.Lib.HelloMainInv
import Spike.Lib.HelloQ
import Spike.Lib.WakeM0Compat
import Spike.Lib.WakeMsOfFields

namespace Spike.Lib.HelloCompat0

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloMainInv (mainInvP mainInvP_closed mainInvP_W mainWRH helloM)
open Spike.Lib.WakeMLive (wlRet)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloQ (helloQ)

/-- At `wlIf` in `mainInvP p` inside `mainWRH`, `d` bound to a number other
than `1` is impossible (`FlagW`'s first fact; `WakeInst.not_flagIf`). -/
theorem not_flagIfH {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {lab : String → Int64} {exe : _root_.Executable} {Λ : Scc.Sem.Layout} {lsize : WeakMem.AllocLabel → Nat}
    {s : State} {env : TermRun.Env} {t : Ty} {n : Nat} (hn : n ≠ 1)
    (h : mainInvP p lbl ms (mainWRH lab exe Λ lbl lsize) s
      ⟨WakeM0.wlIf, ("d", t, [TermRun.cst (.num n)]) :: env, none⟩) : False :=
  have h1 : n < 2 ^ 64 ∧ 1 = n :=
    (mainInvP_W _ _ h).2.2.2.2.1 rfl t (TermRun.cst (.num n)) (by simp [TermRun.lookupE, List.find?])
  hn h1.2.symm

section Fields

variable {ι : Type} (lbl : ι → WeakMem.AllocLabel → Option Nat) (lsize : ι → WeakMem.AllocLabel → Nat)
  (ms : ι → MemSide isaLSE2) (cw : ι → TermRun.Word) (lab : String → Int64) (exe : _root_.Executable)
  (Λ : Scc.Sem.Layout) (μT : Marks)
  (hoff : ∀ s c, Spike.Lib.A64WakeOff.AbOffA lab s c → ∀ k a, μT.abortAt k = some a → pcOf s ≠ a)

/-- `WCompat0.live0`. -/
theorem live0H : ∀ w s c, (helloM lbl lsize ms cw lab exe Λ μT hoff).Mi w s c → c.term ≠ wlRet :=
  fun _ s c h => (mainInvP_W s c h).1.2.1

/-- main's states are wide on `exe` (`wide0`, `sysExec0`). -/
theorem wideXH : ∀ w s c, (helloM lbl lsize ms cw lab exe Λ μT hoff).Mi w s c →
    Spike.Lib.A64.WideKeep.WideX exe s :=
  fun _ s c h => (mainInvP_W s c h).1.2.2.1

/-- `WCompat0.wide0`. -/
theorem wide0H : ∀ w s c, (helloM lbl lsize ms cw lab exe Λ μT hoff).Mi w s c → Scc.Cert.WideA64.WideSt s :=
  fun w s c h => (wideXH lbl lsize ms cw lab exe Λ μT hoff w s c h).1

/-- `WCompat0.sysExec0`. -/
theorem sysExec0H [Kraken.Executable.ValidLayout exe] :
    ∀ w s c t, (helloM lbl lsize ms cw lab exe Λ μT hoff).Mi w s c → abi.atSys s = true →
      isaLSE2.exec s = some t → ∃ m, t = .fault m :=
  WakeMsOf.sysExec_of_exe' (exe := exe) fun w s c h => (wideXH lbl lsize ms cw lab exe Λ μT hoff w s c h).2

/-- `WCompat0.relW0`: main's instructions write at most once, a release
write. -/
theorem relW0H : ∀ w s c e, (helloM lbl lsize ms cw lab exe Λ μT hoff).Mi w s c → isaLSE2.exec s = some e →
    EvTree.RelW1 Arch.armv8 e :=
  fun _ s c _ h he => (mainInvP_W s c h).2.1.2 _ he

/-- `WCompat0.noSite0` from the labels' abort-free states off the marks'
sites (`hns`). -/
theorem noSite0H {μ : Marks} (hns : ∀ s c, Spike.Lib.A64WakeOff.AbOffA lab s c → siteAt abi μ s = none) :
    ∀ w s c, (helloM lbl lsize ms cw lab exe Λ μT hoff).Mi w s c → siteAt abi μ s = none :=
  fun _ s c h => hns s c (mainInvP_W s c h).1.1

/-- `WCompat0.noWrite0`: main's system calls are `futex` or `exit_group`
(`MainSys`), never `write`. -/
theorem noWrite0H : ∀ w s c fd buf n, (helloM lbl lsize ms cw lab exe Λ μT hoff).Mi w s c → abi.atSys s = true →
    decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write fd buf n) := by
  intro _ s c fd buf n h ha
  show decode Nrs.a64 s.st.1.regs.X8.toNat _ ≠ _
  rcases (mainInvP_W s c h).2.2.2.1 ha with h | h <;> rw [h] <;>
    simp [decode, Nrs.a64] <;> repeat (first | split | simp)

/-- `WCompat0.flagLd` (`WakeInst.flagLd_I` at `mainInvP helloSrc`): the
memory side's kernel model `hK`, its runtime addresses off every placed
label `hrt`, its read side taking every number `hrdN`. -/
theorem flagLdH [Kraken.Executable.ValidLayout exe] (hK : ∀ w, (ms w).K = some abi)
    (hrt : ∀ w a, (ms w).rt a → ¬ ∃ l b, lbl w l = some b ∧ b ≤ a ∧ a < b + 8 * lsize w l)
    (hrdN : ∀ w (w' : TermRun.Word) n, w'.val = .num n → (ms w).rd w') :
    ∀ w s c (kl : Kraken.LoadKind) (A : BitVec 64) (k : Val → isaLSE2.State) (ty : Ty) (wd : TermRun.Word),
    (helloM lbl lsize ms cw lab exe Λ μT hoff).Mi w s c → c.term = WakeM0.wlBody →
    isaLSE2.exec s = some (.load kl false ⟨A, 8⟩ fun v => .done (k v)) →
    TermRun.evalAt c.env (.var "c") = some (ty, [wd]) → ValRep ((helloM lbl lsize ms cw lab exe Λ μT hoff).lbl w) wd.val A.toNat →
    (∀ v : Val, (v.setWidth 64).toNat ≠ 1 → (helloM lbl lsize ms cw lab exe Λ μT hoff).Mi w (k v) c) ∧
    (∀ (v : Val) (w' : TermRun.Word), (v.setWidth 64).toNat = 1 → ((helloM lbl lsize ms cw lab exe Λ μT hoff).ms w).rd w' →
      ValRep ((helloM lbl lsize ms cw lab exe Λ μT hoff).lbl w) w'.val 1 →
      (helloM lbl lsize ms cw lab exe Λ μT hoff).Mi w (k v) ⟨WakeM0.wlIf, ("d", loadTy ty, [w']) :: c.env, none⟩) := by
  intro w s c kl A k ty wd h hb he hev hv
  have hW := mainInvP_W s c h
  have hvl : Kraken.Executable.ValidLayout s.exe := hW.1.2.2.1.2 ▸ ‹Kraken.Executable.ValidLayout exe›
  have hb' := hb
  unfold WakeM0.wlBody at hb'
  -- the load's continuation from another row's
  have hk : ∀ {kl' : Kraken.LoadKind} {A' : BitVec 64} {g : Val → State},
      isaLSE2.exec s = some (.load kl' false ⟨A', 8⟩ fun v => .done (g v)) → A' = A ∧ ∀ v, g v = k v := by
    intro kl' A' g he'
    have hx := he'.symm.trans he
    simp only [Option.some.injEq, EvTree.load.injEq, Loc.mk.injEq, true_and, and_true] at hx
    exact ⟨hx.2.1, fun v => by injection congrFun hx.2.2 v⟩
  rcases mainInvP_closed s c h with ⟨o⟩ | ⟨kl', A', g, x, a, e, ty', w0, V, he', ht, hev', -, hn, hy, -⟩
  · cases o with
    | silent _ _ he' => cases he'.symm.trans he
    | choice P t he' hs =>
      cases he'.symm.trans he
      exact hs.elim
    | load kl' A' g x a e ty' w0 he' ht hev' _ hx _ =>
      rw [hb'] at ht; cases ht
      rw [hev] at hev'; cases hev'
      obtain ⟨rfl, hgk⟩ := hk he'
      refine ⟨fun v hv1 => ?_, fun v w' _ hr hr' => hgk v ▸ hx v w' hr (by rwa [‹(v.setWidth 64).toNat = 1›])⟩
      exact (not_flagIfH hv1 (hgk v ▸ hx v (TermRun.cst (.num (v.setWidth 64).toNat))
        (hrdN w _ _ rfl) ⟨BitVec.isLt _, rfl⟩)).elim
    | store _ _ _ _ _ _ _ _ _ _ _ _ he' => cases he'.symm.trans he
    | rtStore _ _ _ _ _ he' => cases he'.symm.trans he
    | rtLoad kl' L g c' he' hrt' =>
      have hx := he'.symm.trans he
      simp only [Option.some.injEq, EvTree.load.injEq] at hx
      obtain ⟨-, -, rfl, -⟩ := hx
      obtain ⟨t, w1, sa, hl, hw, hs, hof⟩ := hW.2.2.2.2.2.1 hb
      have hof' : @LT.lt Nat _ sa.offset (lsize w sa.label) := hof
      rw [show TermRun.evalAt c.env (.var "c") = TermRun.lookupE c.env "c" from rfl, hl] at hev
      cases hev
      rw [hw] at hv
      obtain ⟨-, x0, hx0, hA⟩ := hv
      obtain ⟨b, hbl⟩ := Option.isSome_iff_exists.mp hs
      have hx0' : (lbl w sa.label).map (· + 8 * sa.offset) = some x0 := hx0
      rw [hbl, Option.map_some, Option.some.injEq] at hx0'
      have hx1 : @Eq Nat (b + 8 * sa.offset) x0 := hx0'
      have hA1 : A.toNat = x0 + 0 := hA
      refine (hrt w _ hrt' ⟨sa.label, b, hbl, ?_, ?_⟩).elim
      · show b ≤ A.toNat; omega
      · show A.toNat < b + 8 * lsize w sa.label; omega
    | rtRmw _ _ _ _ _ he' => cases he'.symm.trans he
    | sys K _ hK' ha =>
      cases Option.some.inj (hK'.symm.trans (hK w))
      obtain ⟨_, hf⟩ := Spike.Lib.A64.SvcFault.exec_atSvc hvl ha he
      cases hf
    | holdLoad _ _ _ x sa u v e _ hX =>
      rcases hX.2 with ⟨_, _, _, _, ht, -⟩ | ⟨_, _, _, _, _, _, _, _, _, ht, -⟩ <;> rw [hb'] at ht <;> cases ht
    | xchgStore _ _ _ _ _ _ _ _ _ _ _ _ he' => cases he'.symm.trans he
    | ctrRmw _ _ _ _ _ _ _ he' => cases he'.symm.trans he
    | alloc _ _ _ _ _ _ _ _ _ _ _ _ he' => cases he'.symm.trans he
    | newStore _ _ _ _ _ _ _ _ _ _ _ _ he' => cases he'.symm.trans he
    | emit K _ _ _ _ hK' ha =>
      cases Option.some.inj (hK'.symm.trans (hK w))
      obtain ⟨_, hf⟩ := Spike.Lib.A64.SvcFault.exec_atSvc hvl ha he
      cases hf
    | fence _ _ _ he' _ _ => cases he'.symm.trans he
  · rw [hb'] at ht; cases ht
    rw [hev] at hev'; cases hev'
    obtain ⟨rfl, hgk⟩ := hk he'
    obtain rfl : V = 1 := Classical.byContradiction fun hV => by
      by_cases hVl : V < 2 ^ 64
      · refine not_flagIfH hV (hy (BitVec.ofNat 128 V) (TermRun.cst (.num V)) ?_ (hrdN w _ _ rfl) ⟨hVl, rfl⟩)
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
      · have h1 := hn 1 (by simp; omega)
        obtain ⟨s', hs', hq, h9⟩ := hW.2.2.2.2.2.2.1 hb _ _ A' _ _ hev hv he' 1
        cases hs'
        exact (mainInvP_W _ _ h1).2.2.2.2.2.2.2 hb hq (by rw [h9]; rfl)
    exact ⟨fun v hv1 => hgk v ▸ hn v hv1, fun v w' h1 hr hr' => hgk v ▸ hy v w' h1 hr hr'⟩

end Fields

section Assemble

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isaLSE2}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {D : WSideH ι} {r0 r1 : ι → Range}
  {lbl : ι → WeakMem.AllocLabel → Option Nat} {lsize : ι → WeakMem.AllocLabel → Nat}
  {ms : ι → MemSide isaLSE2} {cw : ι → TermRun.Word} {lab : String → Int64} {exe : _root_.Executable}
  {Λ : Scc.Sem.Layout} {μT : Marks}
  {hoff : ∀ s c, Spike.Lib.A64WakeOff.AbOffA lab s c → ∀ k a, μT.abortAt k = some a → pcOf s ≠ a}

/-- **`WCompat0` at hello's relation and main's side `helloM`** (see the
module doc). -/
theorem hC0H [Kraken.Executable.ValidLayout exe] {μ : Marks} {ΛC : Scc.Sem.Layout}
    /- main's side reads the spawn's placement -/
    (hlbl : ∀ w, lbl w = (SR w).lbl)
    /- the memory side (instance) -/
    (hK : ∀ w, (ms w).K = some abi) (hG : ∀ w, (ms w).G = G w) (hown : ∀ w s, (ms w).own s = [])
    (hmpW : ∀ w L, (ms w).mp L true →
      (Pa w).foot 0 L ∧ ¬ InLabel (SR w).lbl (SR w).lsize L ∧ Consumer1.LocIn ΛC.shared L)
    (hrt : ∀ w a, (ms w).rt a → ¬ ∃ l b, lbl w l = some b ∧ b ≤ a ∧ a < b + 8 * lsize w l)
    (hrdN : ∀ w (w' : TermRun.Word) n, w'.val = .num n → (ms w).rd w')
    (habt : ∀ w s, (ms w).abortAt s → ∃ k a, μ.abortAt k = some a ∧ pcOf s = a)
    /- the marks' sites are off the labels' abort-free states -/
    (hns : ∀ s c, Spike.Lib.A64WakeOff.AbOffA lab s c → siteAt abi μ s = none)
    /- main's pointer word for `c` -/
    (hcw : ∀ w, (cw w).val = .loc (cS w) 0)
    /- the certified no-promise fact at `Pa` -/
    (hnp : ∀ w x (t : Thread isaLSE2) mem, (Pa w).noProm t.st →
      CertOkC Arch.armv8 (certSem abi Arch.armv8 μ x 0) 0 t mem → t.prom = []) :
    WakeM0.WCompat0 (helloQ arch R1 ι SR cT cS pT Pa G passT (helloM lbl lsize ms cw lab exe Λ μT hoff) D r0 r1)
      (helloM lbl lsize ms cw lab exe Λ μT hoff) μ ΛC where
  lbl0 := hlbl
  K0 := hK
  G0 := hG
  own0 := hown
  mpW0 := hmpW
  wide0 := wide0H lbl lsize ms cw lab exe Λ μT hoff
  noSite0 := noSite0H lbl lsize ms cw lab exe Λ μT hoff hns
  sysExec0 := sysExec0H lbl lsize ms cw lab exe Λ μT hoff
  noWrite0 := noWrite0H lbl lsize ms cw lab exe Λ μT hoff
  cw0 := hcw
  live0 := live0H lbl lsize ms cw lab exe Λ μT hoff
  flagLd := flagLdH lbl lsize ms cw lab exe Λ μT hoff hK hrt hrdN
  noProm0 := hnp
  rd1 w w' h := hrdN w w' 1 h
  abortAt0 := habt
  relW0 := relW0H lbl lsize ms cw lab exe Λ μT hoff

end Assemble

end Spike.Lib.HelloCompat0

/-- info: 'Spike.Lib.HelloCompat0.flagLdH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloCompat0.flagLdH

/-- info: 'Spike.Lib.HelloCompat0.hC0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloCompat0.hC0H

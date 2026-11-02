/-
**`WCompat0.flagLd` at the x86-64 instance** (x86-64 twin of
`Spike/Lib/WakeInst.lean`'s `not_flagIf`/`flagLd_I`): at `wlBody` main's
only load of the flag's word is `wc_waitLoop`'s `movq (%rcx), %rax`
(`OutL.load` or `OutL.ldSt`; every other row's event differs, a system call
faults, the address is the flag's, inside its label, not the runtime's); a
value other than `1` would land at `wlIf` with `d` another number (`FlagW`'s
first fact), and an `ldSt` at a value `V ≥ 2^64` would stutter at `q` with
`%rax = 1` (its third and fourth).

- `not_flagIf`: at `wlIf` in `mainInv`, `d` bound to a number other than `1`
  is impossible.
- `flagLd_I`: `WCompat0.flagLd` at `X64WakeInst.wakeM`.

**Where this differs from AArch64**: the loaded register is `%rax`
(`X64WakeMainF.FlagW`; A64 `x9`); a system call's instruction faults by
`X64.SvcFault.exec_atSyscall` (A64 `A64.SvcFault.exec_atSvc`); main's memory
side is `msXW (wakeMs g) T T W` (its runtime words, `rt`, are `wakeMs`'s).
-/
import Spike.Lib.X64WakeInst

namespace Spike.Lib.X64WakeInst

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64WakeA64
open Spike.Lib.X64.Rt (RuntimeLayout)

/-- At `wlIf` in `mainInv`, `d` bound to a number other than `1` is
impossible (`FlagW`'s first fact). -/
theorem not_flagIf {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {lab : String → Int64}
    {exe : _root_.Executable} {Λ : Scc.Sem.Layout} {lsize : WeakMem.AllocLabel → Nat} {s : State}
    {env : TermRun.Env} {t : Ty} {n : Nat} (hn : n ≠ 1)
    (h : mainInv lbl ms (mainWR lab exe Λ lbl lsize) s
      ⟨X64WakeM0.wlIf, ("d", t, [TermRun.cst (.num n)]) :: env, none⟩) : False :=
  have h1 : n < 2 ^ 64 ∧ 1 = n :=
    (mainInv_W _ _ h).2.2.2.2.1 rfl t (TermRun.cst (.num n)) (by simp [TermRun.lookupE, List.find?])
  hn h1.2.symm

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat) (T W : BitVec 64)
  {ok : Gh → Prop} {lab : String → Int64} {μT : Marks}
  {hoff : ∀ s c, Spike.Lib.X64WakeOff.AbOffA lab s c → ∀ k a, μT.abortAt k = some a → pcOf s ≠ a}

local notation "MI" => wakeM hp i T W ok lab μT hoff

/-- `WCompat0.flagLd`: at `wlBody` main's only load of the flag's word is
`wc_waitLoop`'s flag load (`OutL.load` or `OutL.ldSt`); a value other than
`1` would land at `wlIf` with `d` another number (`FlagW`'s first fact), and
an `ldSt` at a value `V ≥ 2^64` would stutter at `q` with `%rax = 1` (its
third and fourth). -/
theorem flagLd_I : ∀ w s c (kl : Kraken.LoadKind) (A : BitVec 64) (k : Val → isa.State) (ty : Ty)
    (wd : TermRun.Word),
    (MI).Mi w s c → c.term = X64WakeM0.wlBody →
    isa.exec s = some (.load kl false ⟨A, 8⟩ fun v => .done (k v)) →
    TermRun.evalAt c.env (.var "c") = some (ty, [wd]) → ValRep ((MI).lbl w) wd.val A.toNat →
    (∀ v : Val, (v.setWidth 64).toNat ≠ 1 → (MI).Mi w (k v) c) ∧
    (∀ (v : Val) (w' : TermRun.Word), (v.setWidth 64).toNat = 1 → ((MI).ms w).rd w' →
      ValRep ((MI).lbl w) w'.val 1 →
      (MI).Mi w (k v) ⟨X64WakeM0.wlIf, ("d", loadTy ty, [w']) :: c.env, none⟩) := by
  intro w s c kl A k ty wd h hb he hev hv
  have hW := mainInv_W s c h
  have hvl : Kraken.Executable.ValidLayout s.exe := hW.1.2.2.1.2 ▸ (RuntimeLayout.ofPlaceWX hp i).valid
  have hb' := hb
  unfold X64WakeM0.wlBody at hb'
  -- the load's continuation from another row's
  have hk : ∀ {kl' : Kraken.LoadKind} {A' : BitVec 64} {g : Val → State},
      isa.exec s = some (.load kl' false ⟨A', 8⟩ fun v => .done (g v)) → A' = A ∧ ∀ v, g v = k v := by
    intro kl' A' g he'
    have hx := he'.symm.trans he
    simp only [Option.some.injEq, EvTree.load.injEq, Loc.mk.injEq, true_and, and_true] at hx
    exact ⟨hx.2.1, fun v => by injection congrFun hx.2.2 v⟩
  rcases mainInv_closed s c h with ⟨o⟩ | ⟨kl', A', g, x, a, e, ty', w0, V, he', ht, hev', -, hn, hy, -⟩
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
      exact (not_flagIf hv1 (hgk v ▸ hx v (TermRun.cst (.num (v.setWidth 64).toNat)) ⟨_, rfl⟩
        ⟨BitVec.isLt _, rfl⟩)).elim
    | store _ _ _ _ _ _ _ _ _ _ _ _ he' => cases he'.symm.trans he
    | rtStore _ _ _ _ _ he' => cases he'.symm.trans he
    | rtLoad kl' L g c' he' hrt =>
      have hx := he'.symm.trans he
      simp only [Option.some.injEq, EvTree.load.injEq] at hx
      obtain ⟨-, -, rfl, -⟩ := hx
      obtain ⟨t, w1, sa, hl, hw, hs, hof⟩ := hW.2.2.2.2.2.1 hb
      have hof' : @LT.lt Nat _ sa.offset (w.1.lsize sa.label) := hof
      rw [show TermRun.evalAt c.env (.var "c") = TermRun.lookupE c.env "c" from rfl, hl] at hev
      cases hev
      rw [hw] at hv
      obtain ⟨-, x0, hx0, hA⟩ := hv
      obtain ⟨b, hbl⟩ := Option.isSome_iff_exists.mp hs
      have hx0' : (w.1.lbl sa.label).map (· + 8 * sa.offset) = some x0 := hx0
      rw [hbl, Option.map_some, Option.some.injEq] at hx0'
      have hx1 : @Eq Nat (b + 8 * sa.offset) x0 := hx0'
      have hA1 : A.toNat = x0 + 0 := hA
      refine (hrt ⟨sa.label, b, hbl, ?_⟩).elim
      show b ≤ A.toNat ∧ A.toNat < b + 8 * w.1.lsize sa.label
      omega
    | rtRmw _ _ _ _ _ he' => cases he'.symm.trans he
    | sys K _ hK ha =>
      cases Option.some.inj (hK.symm.trans (show ((MI).ms w).K = some abi from rfl))
      obtain ⟨_, hf⟩ := Spike.Lib.X64.SvcFault.exec_atSyscall hvl ha he
      cases hf
    | holdLoad _ _ _ x sa u v e _ hX =>
      rcases hX.2 with ⟨_, _, _, _, ht, -⟩ | ⟨_, _, _, _, _, _, _, _, _, ht, -⟩ <;> rw [hb'] at ht <;> cases ht
    | xchgStore _ _ _ _ _ _ _ _ _ _ _ _ he' => cases he'.symm.trans he
    | ctrRmw _ _ _ _ _ _ _ he' => cases he'.symm.trans he
    | alloc _ _ _ _ _ _ _ _ _ _ _ _ he' => cases he'.symm.trans he
    | newStore _ _ _ _ _ _ _ _ _ _ _ _ he' => cases he'.symm.trans he
    | emit K _ _ _ _ hK ha =>
      cases Option.some.inj (hK.symm.trans (show ((MI).ms w).K = some abi from rfl))
      obtain ⟨_, hf⟩ := Spike.Lib.X64.SvcFault.exec_atSyscall hvl ha he
      cases hf
    | fence _ _ _ he' _ _ => cases he'.symm.trans he
  · rw [hb'] at ht; cases ht
    rw [hev] at hev'; cases hev'
    obtain ⟨rfl, hgk⟩ := hk he'
    obtain rfl : V = 1 := Classical.byContradiction fun hV => by
      by_cases hVl : V < 2 ^ 64
      · refine not_flagIf hV (hy (BitVec.ofNat 128 V) (TermRun.cst (.num V)) ?_ ⟨_, rfl⟩ ⟨hVl, rfl⟩)
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
      · have h1 := hn 1 (by simp; omega)
        obtain ⟨s', hs', hq, h9⟩ := hW.2.2.2.2.2.2.1 hb _ _ A' _ _ hev hv he' 1
        cases hs'
        exact (mainInv_W _ _ h1).2.2.2.2.2.2.2 hb hq (by rw [h9]; rfl)
    exact ⟨fun v hv1 => hgk v ▸ hn v hv1, fun v w' h1 hr hr' => hgk v ▸ hy v w' h1 hr hr'⟩

end Inst

end Spike.Lib.X64WakeInst

/-- info: 'Spike.Lib.X64WakeInst.not_flagIf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInst.not_flagIf

/-- info: 'Spike.Lib.X64WakeInst.flagLd_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInst.flagLd_I

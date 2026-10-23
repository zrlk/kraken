/-
`correct_loop_x64` re-derived from the per-construct judgement.

The spinning reader of `Spike/Bridge/X64Loop.lean` (`l: movq (%rdi), %rax;
cmpq $0, %rax; jz l` against `spin f = let r = load acq f in if r = 0 then
spin f else ret r`) as fragments of the relation:

* `HeadF`: at the loop head, the source at the body (`spinBody`, `f`
  bound);
* `CmpF`: at the `cmp`, `rax` holding the value read, the source at the
  test with `r` bound to its low 64 bits;
* `JzF`: at the `jz`, as `CmpF`, the zero flag set iff `rax = 0`;
* `ExitF`: past the `jz`, the source at `ret r`.

The instructions as `Out` (`out_head`, `out_cmp`, `out_jz`): the `movq` is
the source's load; the `cmp` a register operation (the source stutters);
the `jz` the test and the tail call (back to the head, two local steps) or
the test (to the exit, one local step). They compose into the reader's
segment `seg_reader : Seg progL lbl NumMS HeadF ExitF` (`Seg.seq`,
`Seg.loop`), and with its side conditions into `Reader` (`reader`), which
`Spike.Lib.correctS` consumes: `correct_loop_x64'` has the statement of
`correct_loop_x64`.

The instruction rows are the bridge's (`exec_head`, `exec_cmp`, `exec_jz`);
the loop has no straight-line slot code, so the block lemma of
`Spike/Lib/A64Block.lean` has nothing to cover here (the `cmp` alone would
be a one-instruction block).
-/
import Spike.Lib.Thread
import Spike.Bridge.X64Loop

namespace Spike.Lib.X64Loop

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (SrcSem Target ValRep)
open Spike.Bridge (fTy fW envF flagA spinBody testTerm progL spinDecl srcInitL close_fTy asmOf)
open Spike.Bridge.X64 (F st0 sW shape regVal regs layoutΛ flagIn layoutΛ_wf)
open Spike.Bridge.X64Loop (lprog atL st1 rax Head Exit exec_head exec_cmp exec_jz set_rdi set_rax head_st1
  regVal_rdi regVal_rax)

/-- The flag's allocation is placed at `F`. -/
def lbl : WeakMem.AllocLabel → Option Nat := fun l => if l = 0 then some F.toNat else none

theorem valRep_fW {n : Nat} (h : ValRep lbl fW.val n) : n = F.toNat := by
  simpa [fW, TermRun.cst, Promises.TVal.mk0, ValRep, Scc.Sem.wordAddr, lbl, flagA] using h

/-! ## The fragments -/

/-- At the loop head; the source at the body. -/
def HeadF : Frag isa := fun s c => Head s ∧ c = ⟨spinBody, envF, none⟩

/-- At the `cmp` with the value `v` read into `rax`; the source at the test,
`r` bound to `v`'s low 64 bits. -/
def CmpF : Frag isa := fun s c =>
  ∃ (v : Val) (w : TermRun.Word) (r : Reg64s) (fl : StatusFlags), s = atL r fl 0x100001 ∧ r.rdi = 0x1000 ∧
    rax r = v.setWidth 64 ∧
    w.val = .num (v.setWidth 64).toNat ∧ c = ⟨testTerm, ("r", .int, [w]) :: envF, none⟩

/-- At the `jz`: as `CmpF`, the zero flag set iff `rax = 0`. -/
def JzF : Frag isa := fun s c =>
  ∃ (v : Val) (w : TermRun.Word) (r : Reg64s) (fl : StatusFlags), s = atL r fl 0x100002 ∧ r.rdi = 0x1000 ∧
    rax r = v.setWidth 64 ∧
    (CondCode.z.interp fl = true ↔ rax r = 0) ∧ w.val = .num (v.setWidth 64).toNat ∧
    c = ⟨testTerm, ("r", .int, [w]) :: envF, none⟩

/-- Past the `jz`; the source at `ret r`. -/
def ExitF : Frag isa := fun s c =>
  ∃ (v : Val) (w : TermRun.Word), Exit v s ∧ w.val = .num (v.setWidth 64).toNat ∧
    c = ⟨.ret (.var "r"), ("r", .int, [w]) :: envF, none⟩

/-! ## The source's local steps -/

theorem ls_test {w : TermRun.Word} {n : Nat} (hw : w.val = .num n) :
    LocalStep progL ⟨testTerm, ("r", .int, [w]) :: envF, none⟩
      ⟨if n = 0 then .tail "spin" [] (.var "f") else .ret (.var "r"), ("r", .int, [w]) :: envF, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht he _ _
  by_cases hn : n = 0
  · subst hn
    simp [TermRun.tstep, ht, he, testTerm, TermRun.evalAt, TermRun.lookupE, hw, TermRun.cst, Promises.TVal.mk0]
  · simp [TermRun.tstep, ht, he, testTerm, TermRun.evalAt, TermRun.lookupE, hw, TermRun.cst, Promises.TVal.mk0, hn]

theorem ls_tail (w : TermRun.Word) :
    LocalStep progL ⟨.tail "spin" [] (.var "f"), ("r", .int, [w]) :: envF, none⟩ ⟨spinBody, envF, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th hg ht he hσ hst
  simp [TermRun.tstep, ht, he, TermRun.enter, hg, progL, spinDecl, TermRun.evalAt, TermRun.lookupE, envF,
    TermRun.ol, hσ, hst]
  rw [close_fTy]

/-! ## The instructions -/

/-- **The `movq`** is the source's load. -/
theorem out_head {s : State} {c : Ctl} (h : HeadF s c) : Out progL lbl NumMS CmpF s c := by
  obtain ⟨⟨r, fl, rfl, h0⟩, rfl⟩ := h
  refine .load .plain F _ "r" (.var "f") testTerm fTy fW (exec_head r fl h0) rfl rfl ?_
    (fun v w' ⟨n, hn⟩ hval => ?_) ⟨_, rfl⟩
  · simp [fW, TermRun.cst, Promises.TVal.mk0, ValRep, Scc.Sem.wordAddr, lbl, flagA]
  · rw [hn] at hval
    obtain ⟨-, hv⟩ := hval
    exact ⟨v, w', _, fl, rfl, (set_rdi r _).trans h0, set_rax r _, hn.trans (by rw [hv]), rfl⟩

/-- **The `cmp`**: flags only; the source stutters. -/
theorem out_cmp {s : State} {c : Ctl} (h : CmpF s c) : Out progL lbl NumMS JzF s c := by
  obtain ⟨v, w, r, fl, rfl, h0, h2, hw, rfl⟩ := h
  obtain ⟨fl', hex, hz⟩ := exec_cmp r fl
  exact .silent _ _ hex (.refl _) ⟨v, w, r, fl', rfl, h0, h2, hz, hw, rfl⟩

/-- **The `jz`** is the test and the tail call (back to the head) or the
test (to the exit). -/
theorem out_jz {s : State} {c : Ctl} (h : JzF s c) :
    Out progL lbl NumMS (fun s c => HeadF s c ∨ ExitF s c) s c := by
  obtain ⟨v, w, r, fl, rfl, h0, h2, hz, hw, rfl⟩ := h
  refine .silent _ (if (v.setWidth 64).toNat = 0 then ⟨spinBody, envF, none⟩
    else ⟨.ret (.var "r"), ("r", .int, [w]) :: envF, none⟩)
    (exec_jz r fl) ?_ ?_
  · by_cases hz0 : (v.setWidth 64).toNat = 0
    · simp only [hz0, ↓reduceIte]
      have := ls_test hw
      simp only [hz0, ↓reduceIte] at this
      exact .step this (.single (ls_tail w))
    · simp only [hz0, ↓reduceIte]
      have := ls_test hw
      simp only [hz0, ↓reduceIte] at this
      exact .single this
  · rw [h2] at hz
    by_cases hv : v.setWidth 64 = 0
    · have hz0 : (v.setWidth 64).toNat = 0 := by rw [hv]; rfl
      simp only [hz.mpr hv, hz0, ↓reduceIte]
      exact .inl ⟨⟨r, fl, rfl, h0⟩, rfl⟩
    · have hz0 : (v.setWidth 64).toNat ≠ 0 := fun h => hv (BitVec.eq_of_toNat_eq (by simpa using h))
      have hf : CondCode.z.interp fl = false := by
        cases h : CondCode.z.interp fl
        · rfl
        · exact absurd (hz.mp h) hv
      simp only [hf, hz0, Bool.false_eq_true, ↓reduceIte]
      exact .inr ⟨v, w, ⟨r, fl, rfl, h0, h2⟩, hw, rfl⟩

/-- **The reader's segment**, composed: the `movq`, the `cmp`, the `jz`,
looped on the back edge. -/
theorem seg_reader : Seg progL lbl NumMS HeadF ExitF :=
  Seg.loop (Seg.seq (Seg.step fun _ _ => out_head) (Seg.seq (Seg.step fun _ _ => out_cmp)
    (Seg.step fun _ _ => out_jz)))

/-! ## The consumer's inputs -/

/-- The reader's invariant: the head, the `cmp`, the `jz`. -/
def Inv : Frag isa := fun s c => HeadF s c ∨ CmpF s c ∨ JzF s c

/-- **The reader.** -/
theorem reader : Reader progL lbl F Inv ExitF where
  out s c h := by
    rcases h with h | h | h
    · exact (out_head h).mono fun s c h => .inl (.inr (.inl h))
    · exact (out_cmp h).mono fun s c h => .inl (.inr (.inr h))
    · exact (out_jz h).mono fun s c h => h.elim (fun h => .inl (.inl h)) .inr
  fin := by
    rintro _ _ ⟨v, w, ⟨r, fl, rfl, -, -⟩, -, -⟩
    exact Spike.Bridge.X64.exec_end (by show ((0x100003 : Int64) == 0x100000 + 3) = true; decide)
  noStore := by
    rintro s c (⟨-, rfl⟩ | ⟨v, w, r, fl, -, -, -, -, rfl⟩ | ⟨v, w, r, fl, -, -, -, -, -, rfl⟩) x a b e h <;>
      simp [spinBody, testTerm] at h
  noXchg := by
    rintro s c hc x sa u v e ⟨-, ⟨_, _, _, _, h, -⟩ | ⟨_, _, _, _, _, _, _, _, _, h, -⟩⟩ <;>
      rcases hc with (⟨-, rfl⟩ | ⟨v, w, r, fl, -, -, -, -, rfl⟩ | ⟨v, w, r, fl, -, -, -, -, -, rfl⟩) <;>
      simp [spinBody, testTerm] at h
  noAlloc := by
    rintro s c (⟨-, rfl⟩ | ⟨v, w, r, fl, -, -, -, -, rfl⟩ | ⟨v, w, r, fl, -, -, -, -, -, rfl⟩) x a τ e h <;>
      simp [spinBody, testTerm] at h
  flag := by
    rintro s c (⟨-, rfl⟩ | ⟨v, w, r, fl, -, -, -, -, rfl⟩ | ⟨v, w, r, fl, -, -, -, -, -, rfl⟩) x a e h
    · simp only [spinBody, Expr.let_.injEq, Op.load.injEq, true_and] at h
      obtain ⟨-, rfl, -⟩ := h
      rfl
    · simp [testTerm] at h
    · simp [testTerm] at h
  addr _ h := valRep_fW h

/-- The test's value as a 64-bit value. -/
theorem val64 (v : Val) : ((v.setWidth 64).setWidth 128 : Val).toNat < 2 ^ 64 ∧
    ((v.setWidth 64).setWidth 128 : Val).setWidth 64 = v.setWidth 64 ∧
    ((v.setWidth 64).setWidth 128 : Val).toNat = (v.setWidth 64).toNat := by
  have h := (v.setWidth 64).isLt
  have h1 : ((v.setWidth 64).setWidth 128 : Val).toNat = (v.setWidth 64).toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨h1 ▸ h, BitVec.eq_of_toNat_eq ?_, h1⟩
  rw [BitVec.toNat_setWidth, h1, BitVec.toNat_setWidth]
  exact Nat.mod_mod _ _

theorem place_r {v : Val} {w : TermRun.Word} {r : Reg64s} {fl : StatusFlags} {pc : Int64}
    (h2 : rax r = v.setWidth 64) (hw : w.val = .num (v.setWidth 64).toNat) :
    ∃ (v' : Val) (w' : TermRun.Word), ("r", Ty.int, [w]) :: envF = ("r", .int, [w']) :: envF ∧
      w'.val = .num v'.toNat ∧ v'.toNat < 2 ^ 64 ∧ regVal (atL r fl pc) (.r .rax) = v'.setWidth 64 :=
  ⟨(v.setWidth 64).setWidth 128, w, rfl, by rw [hw, (val64 v).2.2], (val64 v).1,
    by rw [(val64 v).2.1]; exact (regVal_rax r fl _).trans h2⟩

/-- **Where the fragments place the source words**: `rdi` the flag's
address, `rax` the value read. -/
theorem place : Place regVal F st0 sW (RegId.r .rdi) (RegId.r .rax) Inv ExitF where
  f0 := regs.f0
  fW := regs.fW
  frame := by
    rintro s c ((⟨⟨r, fl, rfl, h0⟩, rfl⟩ | ⟨v, w, r, fl, rfl, h0, h2, hw, rfl⟩ |
      ⟨v, w, r, fl, rfl, h0, h2, -, hw, rfl⟩) | ⟨v, w, ⟨r, fl, rfl, h0, h2⟩, hw, rfl⟩)
    · exact ⟨regVal_rdi r fl _ h0, .inl rfl⟩
    · exact ⟨regVal_rdi r fl _ h0, .inr (place_r h2 hw)⟩
    · exact ⟨regVal_rdi r fl _ h0, .inr (place_r h2 hw)⟩
    · exact ⟨regVal_rdi r fl _ h0, .inr (place_r h2 hw)⟩

theorem head_init : HeadF st1 ⟨spinBody, envF, none⟩ := ⟨head_st1, rfl⟩

theorem srcInit_eq : srcInitS ⟨spinBody, envF, none⟩ = srcInitL := rfl

variable {k : Promises.Knobs} {arch : WeakMem.Arch}

/-- **`correct_loop_x64` from the judgement**: the statement of
`Spike.Bridge.X64Loop.correct_loop_x64`, proved by `Spike.Lib.correctS` from
the reader's fragments. -/
theorem correct_loop_x64' (pl : State → BitVec 64 → Option (BitVec 64)) (B : Scc.Sem.Budget) :
    Scc.Sem.Correct (Target.ofBase isa Arch.tso regVal pl) (SrcSem.ofStep progL k arch (· = srcInitL))
      layoutΛ B (asmOf st0 st1 F) :=
  correctS Arch.tso reader shape.toWShape (.inl head_init) place flagIn layoutΛ_wf B rfl

theorem correct_loop_x64'_type :
    type_of% @correct_loop_x64' = type_of% @Spike.Bridge.X64Loop.correct_loop_x64 := rfl

end Spike.Lib.X64Loop

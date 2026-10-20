/-
**Part 6: the x64 `treiber_pp.kl`
threads make only release writes**: `treiberPusherX_noNT` and
`treiberPopperX_noNT`, each thread in
`(relPureQ Arch.tso (fun _ _ => False)).within S` (the pusher at `pushS`,
the popper at `sAll`), by one `cfgEnv_partial` table and `vcgen`. Under
`Arch.tso` the `lock cmpxchgq` (an `.acqRel` RMW) and the plain `movl`/`movq`
stores are releases, so the purity obligation is vacuous; the tables carry
the frame. The x64 counterpart of the Treiber proof's `EnvG/TreiberRelPure.lean` (as
`EnvG/X64CmpxRelPure.lean` is of the spinlock's).

Also the start states `StartPushX`, `StartPopX` and the purity
specifications `treiberPushNoNTSpec`, `treiberPopNoNTSpec` with their
`_holds` lemmas.
-/
import Kraken.Promising.SLR.EnvG.RelPureEnvX64
import Kraken.Promising.SLR.EnvG.X64TreiberVCGen

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG

namespace Kraken.Promising.X64.EnvG.TreiberX

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The all-release environment on a layout `S`. -/
abbrev EnvRT (S : SharedEnv.Layout) : SharedEnv := (SharedEnv.relPureQ Arch.tso fun _ _ => False).within S

section Pusher

variable [layout : _root_.Layout]

variable [Executable.ValidLayout (layout treiberPusherX)]

local instance treiberPusherX.envR : CodeEnv := ⟨layout treiberPusherX⟩

/-- **The x64 pusher makes only release writes** (counted, partial). -/
theorem treiberPusherX_noNT (t n : BitVec 64) :
    PartialTripleEnv (SharedEnv.counted (EnvRT (pushS t n))) (fun s _ => PFrameX t n s) treiberPusherX
      (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (fun (_ : Label) s (_ : (SharedEnv.counted (EnvRT (pushS t n))).State) =>
    PFrameX t n s) (hP := by funext s g; simp)
  cfg_cases_env [treiberPusherX]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hdt, hdd, hdn⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [Reg64s.get64] at hx0 hx1
  all_goals have hdn' : Mem.loadInt _ (n + 8#64) 8 = none := hdn
  -- cut `pusher`
  case vc1 => simp [hx1, hdd]
  case vc2 =>
    simp only [SharedEnv.counted_ok]
    simp [hx1]
    first | trivial | exact fun h => absurd rfl h | exact fun h => h rfl | (simp [SharedEnv.relPureQ]; done)
  case vc3 => exact ⟨by simp [hx0], by simp [hx1], hdt, hdd, hdn⟩
  -- cut `push`
  case vc1 =>
    simp only [SharedEnv.counted_ok]
    simp [hx0]
    first | trivial | exact fun h => absurd rfl h | exact fun h => h rfl | (simp [SharedEnv.relPureQ]; done)
  case vc2 =>
    simp only [SharedEnv.counted_ok]
    simp [hx1]
    first | trivial | exact fun h => absurd rfl h | exact fun h => h rfl | (simp [SharedEnv.relPureQ]; done)
  case vc3 =>
    rename_i v σ1 hld dm σ2 hst _
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, -⟩ := hst
    subst hdm
    simp [hx0, hdt]
  case vc4 =>
    rename_i v σ1 hld dm σ2 hst _
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, -⟩ := hst
    subst hdm
    simp only [SharedEnv.counted_ok]
    simp [hx0]
    first | trivial | exact fun h => absurd rfl h | exact fun h => h rfl | (simp [SharedEnv.relPureQ]; done)
  case vc5 =>
    rename_i σ v σ1 hld dm σ2 hst old σ3 hcas heq hz _
    have h1 : σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        omega
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, -, hst2⟩ := hst
    subst hdm
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd (by rw [heq]; exact BitVec.sub_self _) hz
  case vc6 =>
    rename_i σ v σ1 hld dm σ2 hst old σ3 hcas heq hz _
    have h1 : σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        omega
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, -, hst2⟩ := hst
    subst hdm
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simpa using hdt, by simpa using hdd, by simpa using hdn⟩, .inl (by decide)⟩
  case vc7 =>
    rename_i σ v σ1 hld dm σ2 hst old σ3 hcas heq hz _
    have h1 : σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        omega
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, -, hst2⟩ := hst
    subst hdm
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simpa using hdt, by simpa using hdd, by simpa using hdn⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    omega
  case vc8 =>
    rename_i σ v σ1 hld dm σ2 hst old σ3 hcas heq hz _
    have h1 : σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        omega
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, -, hst2⟩ := hst
    subst hdm
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd (by bv_omega) heq

end Pusher

section Popper

variable [layout : _root_.Layout]

variable [Executable.ValidLayout (layout treiberPopperX)]

local instance treiberPopperX.envR : CodeEnv := ⟨layout treiberPopperX⟩

/-- **The x64 popper makes only release writes** (counted, partial). -/
theorem treiberPopperX_noNT (t : BitVec 64) :
    PartialTripleEnv (SharedEnv.counted (EnvRT sAll)) (fun s _ => QFrameX t s) treiberPopperX
      (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (fun (_ : Label) s (_ : (SharedEnv.counted (EnvRT sAll)).State) =>
    QFrameX t s) (hP := by funext s g; simp)
  cfg_cases_env [treiberPopperX]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hd8, hd4⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [Reg64s.get64] at hx0
  case vc1 =>
    simp only [SharedEnv.counted_ok]
    refine ⟨?_, by first | exact mem_sAll8 _ | exact mem_sAll4 _⟩
    simp
    first | trivial | exact fun h => absurd rfl h | exact fun h => h rfl | (simp [SharedEnv.relPureQ]; done)
  case vc2 =>
    rename_i σ v σ1 hld af hz _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd8, by simpa using hd4⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
    · simp [hd8] at hm
    · have h1 := hst.2
      simp only [SharedAccess.tick] at h1
      omega
  case vc3 =>
    simp only [SharedEnv.counted_ok]
    refine ⟨?_, by first | exact mem_sAll8 _ | exact mem_sAll4 _⟩
    simp
    first | trivial | exact fun h => absurd rfl h | exact fun h => h rfl | (simp [SharedEnv.relPureQ]; done)
  case vc4 => simp [hd8]
  case vc5 =>
    simp only [SharedEnv.counted_ok]
    refine ⟨?_, by first | exact mem_sAll8 _ | exact mem_sAll4 _⟩
    simp
    first | trivial | exact fun h => absurd rfl h | exact fun h => h rfl | (simp [SharedEnv.relPureQ]; done)
  case vc6 =>
    rename_i σ v σ1 hld af hz v4 σ4 hld2 old σ5 hcas heq hz2 _
    have h1 : σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        omega
    have h2 : σ1.2 ≤ σ4.2 := by
      rcases hld2 with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        omega
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd8, by simpa using hd4⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    omega
  case vc7 =>
    simp only [SharedEnv.counted_ok]
    refine ⟨?_, by first | exact mem_sAll8 _ | exact mem_sAll4 _⟩
    simp
    first | trivial | exact fun h => absurd rfl h | exact fun h => h rfl | (simp [SharedEnv.relPureQ]; done)
  case vc8 => exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd8, by simpa using hd4⟩, .inl (by decide)⟩
  case vc9 =>
    rename_i σ v σ1 hld af hz v4 σ4 hld2 old σ5 hcas heq hz2 _
    have h1 : σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        omega
    have h2 : σ1.2 ≤ σ4.2 := by
      rcases hld2 with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        omega
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd8, by simpa using hd4⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    omega
  case vc10 =>
    simp only [SharedEnv.counted_ok]
    refine ⟨?_, by first | exact mem_sAll8 _ | exact mem_sAll4 _⟩
    simp
    first | trivial | exact fun h => absurd rfl h | exact fun h => h rfl | (simp [SharedEnv.relPureQ]; done)
  case vc11 => exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd8, by simpa using hd4⟩, .inl (by decide)⟩

end Popper

/-! ## Start states and the purity specifications -/

section Start

variable [layout : _root_.Layout]

/-- **The x64 pusher's start state** (`0:%rdi=top; 0:%rbx=n1`): at the start
of `treiberPusherX` with `rdi = t`, `rbx = n`; no private copy of `top` or
of the node's words. -/
structure StartPushX (t n : BitVec 64) (s : State) : Prop where
  exe : s.exe = layout treiberPusherX
  decls : s.decls = {}
  endPc : s.endPc = (layout treiberPusherX).addrOf treiberPusherX.length
  pc : s.st.2 = (layout treiberPusherX).addrOf 0
  rdi : s.st.1.regs.get64 .rdi = t
  rbx : s.st.1.regs.get64 .rbx = n
  split : Split (pushS t n) s.st.1.dmem

theorem StartPushX.frame {t n : BitVec 64} {s : State} (h : StartPushX t n s) : PFrameX t n s.st.1 :=
  ⟨h.rdi, h.rbx, h.split.loadInt_none (by simp) (by decide) (by decide),
    h.split.loadInt_none (by simp) (by decide) (by decide), h.split.loadInt_none (by simp) (by decide) (by decide)⟩

/-- **The x64 popper's start state** (`1:%rdi=top`): at the start of
`treiberPopperX` with `rdi = t`; a private memory that maps no byte (the
popper's layout is `sAll`). -/
structure StartPopX (t : BitVec 64) (s : State) : Prop where
  exe : s.exe = layout treiberPopperX
  decls : s.decls = {}
  endPc : s.endPc = (layout treiberPopperX).addrOf treiberPopperX.length
  pc : s.st.2 = (layout treiberPopperX).addrOf 0
  rdi : s.st.1.regs.get64 .rdi = t
  dmem : ∀ k, s.st.1.dmem.get? k = none

theorem StartPopX.split {t : BitVec 64} {s : State} (h : StartPopX t s) : Split sAll s.st.1.dmem :=
  split_sAll h.dmem

theorem StartPopX.frame {t : BitVec 64} {s : State} (h : StartPopX t s) : QFrameX t s.st.1 :=
  ⟨h.rdi, fun a => h.split.loadInt_none (mem_sAll8 a) (by decide) (by decide),
    fun a => h.split.loadInt_none (mem_sAll4 a) (by decide) (by decide)⟩

end Start

/-- The threads' all-release specifications: the pusher (layout `lP`, at
`pushS`) at thread `0`, the popper (layout `lQ`, at `sAll`) elsewhere. -/
noncomputable def treiberNoNTSpecX (lP lQ : _root_.Layout) [Executable.ValidLayout (lP treiberPusherX)]
    [Executable.ValidLayout (lQ treiberPopperX)] (t n : BitVec 64) :
    Nat → RelPureSpecQX Arch.tso fun _ _ => False
  | 0 => RelPureSpecQX.ofProgram (layout := lP) (pushS t n) (pushS_le16 t n) treiberPusherX fun _ _ => ∃ _ : Nat, True
  | _ + 1 => RelPureSpecQX.ofProgram (layout := lQ) sAll sAll_le16 treiberPopperX fun _ _ => ∃ _ : Nat, True

/-- **The all-release specifications hold at the start states.** -/
theorem treiberNoNTSpecX_init (lP lQ : _root_.Layout) [Executable.ValidLayout (lP treiberPusherX)]
    [Executable.ValidLayout (lQ treiberPopperX)] {t n : BitVec 64} {sP sQ : State}
    (hP : StartPushX (layout := lP) t n sP) (hQ : StartPopX (layout := lQ) t sQ) :
    ∀ tid s, [sP, sQ][tid]? = some s → (treiberNoNTSpecX lP lQ t n tid).Holds s
  | 0, s, hs => by
    cases hs
    letI : CodeEnv := ⟨lP treiberPusherX⟩
    have hfr := StartPushX.frame (layout := lP) hP
    obtain ⟨he, hds, hend, hpc, -, -, hsp⟩ := hP
    exact RelPureSpecQX.holds_of_partialTripleEnv (layout := lP) (treiberPusherX_noNT (layout := lP) t n).uncount
      rfl he hds hend hpc hsp ⟨0, hfr⟩
  | 1, s, hs => by
    cases hs
    letI : CodeEnv := ⟨lQ treiberPopperX⟩
    have hfr := StartPopX.frame (layout := lQ) hQ
    have hsp := StartPopX.split (layout := lQ) hQ
    obtain ⟨he, hds, hend, hpc, -, -⟩ := hQ
    exact RelPureSpecQX.holds_of_partialTripleEnv (layout := lQ) (treiberPopperX_noNT (layout := lQ) t).uncount
      rfl he hds hend hpc hsp ⟨0, hfr⟩
  | _ + 2, _, hs => by cases hs

end Kraken.Promising.X64.EnvG.TreiberX

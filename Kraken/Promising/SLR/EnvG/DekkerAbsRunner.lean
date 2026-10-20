/-
**`dekker_mfence.kl` from the runner's exact configuration**: `x64_dekker_public_runner`, `x64_dekker_public_verbatim` for threads
that carry the `.kl` runner's declarations (the header types `flag0`,
`flag1` and `counter` `uint32_t`: strict sized, `Decls.Sized`), and its
concrete instance `x64_dekker_public_runner_concrete` at the runner's own
threads and initial memory (`runnerMatchesD`: declarations and initial
memory included).

The proof is `DekkerAbsPublic`'s with the D forms of
`EnvG/X64DeclsLink.lean`: `dkRuleVD` (`ThreadRuleRX.ofSafelyEnvGXMD` at
`MaskOf.refl`), `invDV_initD` (`invGXMD_init`), `dkNoNTSpecsV_initD`
(`RelPureSpecQX.HoldsD`), `final_of_relPureSafelyQX_tsoD`. The old theorems
are unchanged.
-/
import Kraken.Promising.SLR.EnvG.DekkerAbsPublic
import Kraken.Promising.SLR.EnvG.DekkerAbsConcrete
import Kraken.Promising.SLR.EnvG.X64DeclsLink
import Kraken.Promising.SLR.EnvG.X64RunnerCommon

namespace Kraken.Promising.X64.EnvG.DekkerAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvG.Dekker
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Dekker

variable [layout : _root_.Layout] [Executable.ValidLayout (layout dkImageV)]

/-! ## The rule and the start, with declarations -/

/-- **The verbatim Dekker worker's rule with strict sized declarations
`ds`** (`dkRuleV` through `ofSafelyEnvGXMD`). -/
def dkRuleVD {ds : Decls} (hsz : ds.Sized) (tid : Nat) (f o c : BitVec 64)
    {B : Config isa → Res → Ghost → Prop} (hB : ∀ cfg r g, DkThreadEnd tid f o c cfg r → B cfg r g) :
    ThreadRuleRX (I := isa) Arch.tso B tid :=
  ThreadRuleRX.ofSafelyEnvGXMD (S := dkS f o c) (post := postDV tid f o c) hsz (MaskOf.refl _) dkPlan_valid
    (dkS_le16 f o c) dkImageV_phase1 (postDV_end tid f o c) (dkImageV_stuck _)
    (fun cfg t r g cl σ h1 h2 h3 h4 => hB cfg r g (hB_DV tid f o c cfg t r g cl σ h1 h2 h3 h4))

/-- **A verbatim Dekker worker at its start with declarations `ds`**
(`StartDV` with `decls = ds`). -/
structure StartDVD (ds : Decls) (f o : BitVec 64) (s : State) : Prop where
  exe : s.exe = layout dkImageV
  decls : s.decls = ds
  pc : s.st.2 = (_root_.Executable.labels s.exe).label "worker"
  endPc : s.endPc = (_root_.Executable.labels s.exe).label "done"
  rsi : s.st.1.regs.get64 .rsi = f
  rdi : s.st.1.regs.get64 .rdi = o
  split : Split (dkS f o (symD "counter")) s.st.1.dmem

omit [Executable.ValidLayout (layout dkImageV)] in
theorem StartDVD.frame {ds : Decls} {f o : BitVec 64} {s : State} (h : StartDVD ds f o s) :
    FrameDV f o (symD "counter") s.st.1 :=
  ⟨h.rsi, h.rdi, h.split.loadInt_none (by simp) (by decide) (by decide),
    h.split.loadInt_none (by simp) (by decide) (by decide), h.split.loadInt_none (by simp) (by decide) (by decide)⟩

omit [Executable.ValidLayout (layout dkImageV)] in
theorem StartDVD.st {ds : Decls} {f o : BitVec 64} {s : State} (h : StartDVD ds f o s) :
    s.st = (s.st.1, labD "worker") := by
  refine Prod.ext rfl ?_; rw [h.pc, h.exe]

/-- **A verbatim worker's initial invariant with declarations.** -/
theorem invDV_initD {ds : Decls} (hsz : ds.Sized) (tid : Nat) {f o : BitVec 64} (hL : Locs f o (symD "counter"))
    {B : Config isa → Res → Ghost → Prop} (hB : ∀ cfg r g, DkThreadEnd tid f o (symD "counter") cfg r → B cfg r g)
    {ss : List isa.State} {initMem : List (Loc × Val)} {s : isa.State} (hs : ss[tid]? = some s)
    (hS : StartDVD ds f o s) (hf0 : (Config.init ss initMem).mem.initVal ⟨f, 4⟩ = 0)
    (hc0 : (Config.init ss initMem).mem.initVal ⟨symD "counter", 4⟩ = 0) :
    (dkRuleVD hsz tid f o (symD "counter") hB).Inv True (Config.init ss initMem)
      (Res.initOf (Config.init ss initMem).mem (dkFrac ⟨f, 4⟩ ⟨symD "counter", 4⟩) (dkFrac_nonneg _ _))
      dkGhost := by
  have hend : s.endPc = labD "done" := by rw [hS.endPc, hS.exe]
  have hsafe := SpinAbs.Safely.uncountV
    (dkWorkerV_envG tid f o (symD "counter") rfl hL s.st.1
      (σInitX (Config.init ss initMem)
        (Res.initOf (Config.init ss initMem).mem (dkFrac ⟨f, 4⟩ ⟨symD "counter", 4⟩) (dkFrac_nonneg _ _))
        dkGhost, 0)
      ⟨hS.frame, d0_init (g := dkGhost) hL (fun _ => rfl) hf0 hc0⟩)
  rw [← hS.st] at hsafe
  exact invGXMD_init (S := dkS f o (symD "counter")) (e := layout dkImageV) (e' := layout dkImageV)
    (endPc := labD "done") (post := postDV tid f o (symD "counter")) hs rfl
    ⟨hS.exe, hS.decls, hend, hS.split, hsafe⟩

/-- **The `NPSafe` side for verbatim Dekker with declarations.** -/
theorem x64_dekker_npSafe_runner {ds : Decls} (hsz : ds.Sized)
    (hL : Locs (symD "flag0") (symD "flag1") (symD "counter"))
    {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartDVD ds (symD "flag0") (symD "flag1") s0) (h1 : StartDVD ds (symD "flag1") (symD "flag0") s1)
    (hF0 : (Config.init [s0, s1] initMem).mem.initVal ⟨symD "flag0", 4⟩ = 0)
    (hF1 : (Config.init [s0, s1] initMem).mem.initVal ⟨symD "flag1", 4⟩ = 0)
    (hC : (Config.init [s0, s1] initMem).mem.initVal ⟨symD "counter", 4⟩ = 0) :
    ∀ tid, tid < [s0, s1].length → ∀ n m,
      NPSafe (model isa) Arch.tso (DkB (symD "flag0") (symD "flag1") (symD "counter")) tid n m True
        (Config.init [s0, s1] initMem)
        (dkRes (Config.init [s0, s1] initMem).mem ⟨symD "flag0", 4⟩ ⟨symD "flag1", 4⟩ ⟨symD "counter", 4⟩ tid)
        dkGhost := by
  intro tid htid n m
  rcases tid with _ | _ | k
  · exact NPSafe.of_ruleRX _ n m _ _ _ _ (invDV_initD hsz 0 hL (fun _ _ _ h => .inl h) rfl h0 hF0 hC)
  · exact NPSafe.of_ruleRX _ n m _ _ _ _
      (invDV_initD hsz 1 ⟨Ne.symm hL.fo, hL.oc, hL.fc⟩ (fun _ _ _ h => .inr h) rfl h1 hF1 hC)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **The all-release specification holds at a start state with
declarations.** -/
theorem dkNoNTSpecV_holdsD {ds : Decls} {f o : BitVec 64} {s : isa.State} (h : StartDVD ds f o s) :
    (dkNoNTSpecV f o).HoldsD ds s := by
  refine ⟨h.exe, by rw [h.endPc, h.exe]; rfl, h.decls, h.split, ?_⟩
  rw [h.st]
  exact SpinAbs.Safely.uncountV (dkWorkerV_noNT _ _ _ rfl s.st.1 ((), 0) h.frame)

theorem dkNoNTSpecsV_initD {ds : Decls} {s0 s1 : isa.State}
    (h0 : StartDVD ds (symD "flag0") (symD "flag1") s0) (h1 : StartDVD ds (symD "flag1") (symD "flag0") s1) :
    ∀ tid s, [s0, s1][tid]? = some s → (dkNoNTSpecsV tid).HoldsD ds s
  | 0, s, hs => by cases hs; exact dkNoNTSpecV_holdsD h0
  | 1, s, hs => by cases hs; exact dkNoNTSpecV_holdsD h1
  | _ + 2, _, hs => by cases hs

/-! ## The theorem -/

/-- **Dekker with `mfence` for x64 under `Arch.tso`, `dekker_mfence.kl`'s
code verbatim, with the runner's declarations**: `x64_dekker_public_verbatim`
for threads whose declarations are strict sized (`ds.Sized`: the `.kl`
runner's, from the typed header). -/
theorem x64_dekker_public_runner {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hL : Locs (symD "flag0") (symD "flag1") (symD "counter"))
    {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartDVD ds (symD "flag0") (symD "flag1") s0) (h1 : StartDVD ds (symD "flag1") (symD "flag0") s1)
    (hF0 : (Config.init [s0, s1] initMem).mem.initVal ⟨symD "flag0", 4⟩ = 0)
    (hF1 : (Config.init [s0, s1] initMem).mem.initVal ⟨symD "flag1", 4⟩ = 0)
    (hC : (Config.init [s0, s1] initMem).mem.initVal ⟨symD "counter", 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) :
    ¬ ((∃ t, cfg.threads[0]? = some t ∧ (t.st.st.1.regs.get64 .rdx).setWidth 32 = 1) ∧
      (∃ t, cfg.threads[1]? = some t ∧ (t.st.st.1.regs.get64 .rdx).setWidth 32 = 1) ∧
      cfg.mem.finalVal ⟨symD "counter", 4⟩ = 1) :=
  final_of_relPureSafelyQX_tsoD fuel (B := DkB (symD "flag0") (symD "flag1") (symD "counter"))
    (Φ := fun c => ¬ ((∃ t, c.threads[0]? = some t ∧ (t.st.st.1.regs.get64 .rdx).setWidth 32 = 1) ∧
      (∃ t, c.threads[1]? = some t ∧ (t.st.st.1.regs.get64 .rdx).setWidth 32 = 1) ∧
      c.mem.finalVal ⟨symD "counter", 4⟩ = 1))
    (erase_dkInit _ hL) pend_dkGhost dkNoNTSpecsV (fun _ => ds) (fun _ => hsz) (dkNoNTSpecsV_initD h0 h1)
    (x64_dekker_npSafe_runner hsz hL h0 h1 hF0 hF1 hC) hc hf
    fun _ _ E' _ hsize hB ⟨e0, e1, hv⟩ => dk_final hL E' hf hsize hB e0 e1 hv

end Kraken.Promising.X64.EnvG.DekkerAbs

/-! ## The runner's configuration -/

namespace Kraken.Promising.X64.EnvG.DekkerAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.DekkerAbs Kraken.Promising.SLR.EnvG

/-- The runner's declarations for the typed `dekker_mfence.kl`: `flag0`,
`flag1`, `counter`, 4-byte words (strict). -/
def dkDeclsD : Decls := { locs := [⟨0x1000000, 4⟩, ⟨0x1000100, 4⟩, ⟨0x1000200, 4⟩], unsizedDefault := false }

theorem dkDeclsD_sized : dkDeclsD.Sized := ⟨rfl, by decide⟩

/-- The threads as the runner prepares them: `dk0`/`dk1` with the runner's
declarations. -/
def dk0D : X64.State := { dk0 with decls := dkDeclsD }
def dk1D : X64.State := { dk1 with decls := dkDeclsD }

/-- The runner's configuration is `Config.init [dk0D, dk1D] dkInitMemV` in
everything the theorem reads (declarations and initial memory included). -/
def runnerMatchesD (src : String) : Bool :=
  runnerMatchesDL src [dk0D, dk1D] dkInitMemV

/-- info: true -/
#guard_msgs in
#eval runnerMatchesD dekkerKl

section
attribute [local instance] dkLayoutV

theorem dkThreadD_start (f o : BitVec 64) : StartDVD dkDeclsD f o { dkThreadV f o with decls := dkDeclsD } :=
  ⟨rfl, rfl, by show (0x100000 : Int64) = labD "worker"; rw [labD_at 0]; decide,
    by show (0x100000 + 12 : Int64) = labD "done"; rw [labD_at 13]; decide,
    by simp [dkThreadV, Reg64s.get64, Reg64s.set64], by simp [dkThreadV, Reg64s.get64, Reg64s.set64],
    Split.empty _⟩

/-- **Dekker with `mfence`, `dekker_mfence.kl`'s code verbatim, from the
runner's exact configuration**: no final configuration under `Arch.tso` has
both threads' `edx` at `1` and the counter at `1`. -/
theorem x64_dekker_public_runner_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [dk0D, dk1D] dkInitMemV) c) (hf : c.final = true) :
    ¬ ((∃ t, c.threads[0]? = some t ∧ (t.st.st.1.regs.get64 .rdx).setWidth 32 = 1) ∧
      (∃ t, c.threads[1]? = some t ∧ (t.st.st.1.regs.get64 .rdx).setWidth 32 = 1) ∧
      c.mem.finalVal ⟨0x1000200, 4⟩ = 1) := by
  have h0 : StartDVD dkDeclsD (symD "flag0") (symD "flag1") dk0D := by
    rw [symD_flag0, symD_flag1]; exact dkThreadD_start _ _
  have h1 : StartDVD dkDeclsD (symD "flag1") (symD "flag0") dk1D := by
    rw [symD_flag0, symD_flag1]; exact dkThreadD_start _ _
  have h := x64_dekker_public_runner dkDeclsD_sized
    (by rw [symD_flag0, symD_flag1, symD_counter]; exact ⟨by decide, by decide, by decide⟩) h0 h1
    (by rw [symD_flag0]; simp only [Config.init_mem]; decide)
    (by rw [symD_flag1]; simp only [Config.init_mem]; decide)
    (by rw [symD_counter]; simp only [Config.init_mem]; decide) hc hf
  rwa [symD_counter] at h

end

end Kraken.Promising.X64.EnvG.DekkerAbs.Concrete

#print axioms Kraken.Promising.X64.EnvG.DekkerAbs.x64_dekker_public_runner
#print axioms Kraken.Promising.X64.EnvG.DekkerAbs.Concrete.x64_dekker_public_runner_concrete

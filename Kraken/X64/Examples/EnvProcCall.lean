import Kraken.EnvVCGen
import Kraken.X64.Parser
import Kraken.SeparationMem

/-!
# A procedure call over the environment wp

`fetchIncCall` calls a procedure `fetch_inc` that fetches-and-adds a shared
counter at `(%rdi)` with `lock xaddq` and returns. The procedure gets an
environment spec, `Executable.ProcSpecEnv` in `SharedEnv.lastWrite`, from a
`TripleEnv` on its body (`ProcSpecEnv.of_tripleEnv`; the body's `ret` is the
exit channel at the return address, `ret_env_spec`). The caller steps its
`call` through that spec with `vcgen [hc]`, `hc := call_proc_env_spec_at v
"fetch_inc" hproc` (the environment twin of `call_proc_spec_at`): the
return address goes to a mapped stack slot, the callee's postcondition (the
counter's new value, the old one in `rax`) continues the caller's tail.
-/

open Std.WP
open Kraken
open MachineWP

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- A store to bytes that are all mapped maps no new byte. -/
private theorem subDom_storeInt_of_mapped {m : Mem 64} {b : BitVec 64} {n : Nat} {v : Int}
    (hb : (m.loadInt b n).isSome = true) : Mem.SubDom (m.storeInt b n v) m := by
  intro k hk
  simp only [Mem.storeInt, Mem.storeBytes, Std.ExtHashMap.union_eq, Std.ExtHashMap.mem_union_iff] at hk
  rcases hk with hk | hk
  · exact hk
  · obtain ⟨i, hi, rfl⟩ := (mem_At_iff _ _ _).mp hk
    rw [Int.toBytes_length] at hi
    simp only [Mem.loadInt, Option.isSome_map, Mem.loadBytes, List.allSome_isSome_iff,
      List.forall_mem_map] at hb
    have := hb i (List.mem_range.mpr hi)
    rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.isSome_getElem?_iff_mem] at this
    exact this

/-- A load that fails before a store to mapped bytes fails after it. -/
private theorem loadInt_storeInt_of_none {m : Mem 64} {a b : BitVec 64} {n k : Nat} {v : Int}
    (hb : (m.loadInt b n).isSome = true) (ha : m.loadInt a k = none) :
    (m.storeInt b n v).loadInt a k = none := by
  cases h : (m.storeInt b n v).loadInt a k with
  | none => rfl
  | some x =>
    have := Mem.SubDom.loadInt_isSome (subDom_storeInt_of_mapped hb) (by rw [h]; rfl)
    rw [ha] at this
    cases this

section

open Kraken.X64.Parser

variable [layout : _root_.Layout]

/-- The caller, then the procedure it calls, then the end. -/
def fetchIncCall : Program := parse("
caller:
  movq $1, %rax
  call fetch_inc
  addq $1, %rax
  jmp done
fetch_inc:
  lock xaddq %rax, (%rdi)
  ret
done:
  nop
")

/-- The caller's three instructions. -/
abbrev fetchIncCall.caller : Program := parse("
  movq $1, %rax
  call fetch_inc
  addq $1, %rax
")

/-- The procedure's body. -/
abbrev fetchIncCall.body : Program := parse("
  lock xaddq %rax, (%rdi)
  ret
")

local instance fetchIncCall.env : CodeEnv := ⟨layout fetchIncCall⟩

variable [Executable.ValidLayout (layout fetchIncCall)]

/-- The procedure sits at its label. -/
private theorem fetchIncCall_body_placed :
    cenv.sits ((_root_.Executable.labels cenv).label "fetch_inc") fetchIncCall.body :=
  (Program.placed_of_layout (p := fetchIncCall) (by decide) rfl (by decide)).block "fetch_inc"
    ⟨"fetch_inc", fetchIncCall.body, some "done"⟩ rfl

/-- What `fetch_inc` needs at entry, the counter's value being `v`: the
counter at `c = rdi` is shared and the return address `ra` is on the
(mapped) stack. -/
abbrev FetchIncPre (c : BitVec 64) (v : BitVec 64) (ra : Int64) (t : MachineData)
    (g : (SharedEnv.lastWrite [(c, 8)]).State) : Prop :=
  t.regs.get64 .rdi = c ∧ Mem.loadInt t.dmem c 8 = none ∧ (g c).setWidth 64 = v ∧
    ∃ w, Mem.loadInt t.dmem (t.regs.get64 .rsp) 8 = some w ∧ Int64.ofBitVec (BitVec.ofInt 64 w) = ra

/-- What `fetch_inc` leaves: the old value in `rax`, the counter advanced by
the entry `rax`. -/
abbrev FetchIncPost (c : BitVec 64) (v : BitVec 64) (_ra : Int64) (t : MachineData)
    (_g : (SharedEnv.lastWrite [(c, 8)]).State) (s' : MachineData)
    (g' : (SharedEnv.lastWrite [(c, 8)]).State) : Prop :=
  s'.regs.get64 .rax = v ∧ (g' c).setWidth 64 = v + t.regs.get64 .rax

/-- **The procedure's environment spec.** -/
theorem fetchInc_procSpecEnv (c : BitVec 64) :
    cenv.ProcSpecEnv (SharedEnv.lastWrite [(c, 8)])
      ((_root_.Executable.labels cenv).label "fetch_inc") (FetchIncPre c) (FetchIncPost c) := by
  refine Executable.ProcSpecEnv.of_tripleEnv fetchIncCall_body_placed ?_
  rintro v ra t g ⟨hrdi, hnone, hv, w, hw, hra⟩
  apply TripleEnv.of_triple
  vcgen
  all_goals simp_all [SharedEnv.lastWrite, rmwOp128]

/-- **The caller, through the procedure's spec.** From a shared counter at
`c = rdi` holding `v` and a mapped stack slot below `rsp`: `rax` ends with
`v + 1`, and so does the counter. -/
theorem fetchIncCall_correctEnv (c v : BitVec 64) :
    TripleEnv (SharedEnv.lastWrite [(c, 8)])
      (fun s g => s.regs.get64 .rdi = c ∧ Mem.loadInt s.dmem c 8 = none ∧ (g c).setWidth 64 = v ∧
        (Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv) 8).isSome = true)
      fetchIncCall.caller
      (fun s g => s.regs.get64 .rax = v + 1 ∧ (g c).setWidth 64 = v + 1)
      (fun _ _ _ => False) := by
  have hc := call_proc_env_spec_at v "fetch_inc" (fetchInc_procSpecEnv c)
  have h_rt : ∀ (m : DataMem) (a : BitVec 64) (x : Int),
      Mem.loadInt (Mem.storeInt m a 8 x) a 8 = some (Int.ofBytes (Int.toBytes 8 x)) :=
    fun m a x => Mem.loadInt_storeInt m a 8 x (by decide)
  apply TripleEnv.of_triple
  vcgen [hc]
  all_goals simp_all [SharedEnv.lastWrite, BitVec.add_comm]
  -- the push: into the mapped slot, below the shared counter
  rename_i ra m g' hpre hpush
  obtain ⟨-, hnone, hv, hslot⟩ := hpre
  rcases hpush with ⟨rfl, rfl⟩ | ⟨hn, -, -⟩
  · refine ⟨loadInt_storeInt_of_none hslot hnone, hv, _, h_rt _ _ _, ?_⟩
    simpa using Int64.ofBitVec_ofBytes_toBytes ra
  · simp [hn] at hslot

end

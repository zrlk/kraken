/-
Common Kraken executable layout.
-/

namespace Kraken

abbrev Executable (Directive : Type) := Int64 × List (Directive × Nat)

-- JP: why is `size` not `Directive → Nat`?
/-- A layout of a program: its start address and the size of the directive at
each position. Sizes are indexed by position, not by directive, because a
real assembler may give the same directive different sizes at different
positions (x64 branch relaxation, alignment padding). So a `Layout` belongs
to one program: in a multi-thread theorem each thread's program has its own
layout (e.g. `Mp.mp_armv8` takes one for the writer and one for the reader).
`Layout.ofSize` builds the layout in which every directive has a fixed size,
as the runners and the litmus driver do. -/
class Layout (Directive : Type) where
  start : Int64
  size : Nat → Nat

def Layout.apply {Directive : Type} (l : Layout Directive) (prog : List Directive) : Executable Directive :=
  (l.start, prog.mapIdx (fun i d => (d, l.size i)))

instance {Directive : Type} : CoeFun (Layout Directive) (fun _ => List Directive → Executable Directive) where
  coe := Layout.apply

/-- The layout of `prog` at `start` in which every directive `d` takes
`sz d` bytes. -/
@[reducible] def Layout.ofSize {Directive : Type} (start : Int64) (sz : Directive → Nat) (prog : List Directive) :
    Layout Directive where
  start := start
  size i := (prog[i]?.map sz).getD 0

/-- `Layout.ofSize` lays out its program directive by directive. -/
theorem Layout.ofSize_apply {Directive : Type} (start : Int64) (sz : Directive → Nat) (prog : List Directive) :
    Layout.ofSize start sz prog prog = (start, prog.map fun d => (d, sz d)) := by
  show (start, prog.mapIdx fun i d => (d, (prog[i]?.map sz).getD 0)) = _
  congr 1
  apply List.ext_getElem (by simp)
  intro i _ h2
  have hi : i < prog.length := by simpa using h2
  simp [List.getElem_mapIdx, List.getElem?_eq_getElem hi]

-- Returns each directive paired with its start address and size.
-- TODO: tail-recursive version for efficiency?
def Executable.withAddresses {Directive : Type} (e : Executable Directive) : List (Int64 × Directive × Nat) :=
  let (start_addr, ds) := e
  match ds with
  | [] => []
  | (instr, instr_sz) :: ds =>
    (start_addr, instr, instr_sz) :: Executable.withAddresses (start_addr + .ofNat instr_sz, ds)
termination_by e.2

def Executable.directivesAtAddress {Directive : Type} (e : Executable Directive) (a : Int64) : List (Directive × Nat) :=
  let starts_at_a := e.withAddresses.dropWhile (·.1 ≠ a)
  (starts_at_a.takeWhile (·.1 = a)).map (·.2)

def Executable.directivesFromAddress {Directive : Type} (e : Executable Directive) (a : Int64) : List (Directive × Nat) :=
  let starts_at_a := e.withAddresses.dropWhile (·.1 ≠ a)
  starts_at_a.map (·.2)

theorem Executable.withAddresses_map_snd {Directive : Type} (ds : List (Directive × Nat)) (a : Int64) :
    (Executable.withAddresses (a, ds)).map (·.2) = ds := by
  induction ds generalizing a with
  | nil =>
    rw [Executable.withAddresses]
    rfl
  | cons d ds ih =>
    rw [Executable.withAddresses]
    simp [ih]

theorem Executable.withAddresses_dropWhile_start {Directive : Type} (ds : List (Directive × Nat)) (a : Int64) :
    (Executable.withAddresses (a, ds)).dropWhile (fun x => x.1 ≠ a) =
      Executable.withAddresses (a, ds) := by
  cases ds with
  | nil =>
    rw [Executable.withAddresses]
    rfl
  | cons d ds =>
    rw [Executable.withAddresses]
    simp [List.dropWhile]

theorem Executable.directivesFromStart {Directive : Type} [layout : Layout Directive] (prog : List Directive) :
    (layout prog).directivesFromAddress layout.start =
      prog.mapIdx (fun i d => (d, layout.size i)) := by
  dsimp [Executable.directivesFromAddress, Layout.apply]
  rw [Executable.withAddresses_dropWhile_start]
  rw [Executable.withAddresses_map_snd]

theorem directivesAtFromPrefix {Directive : Type} (e: Executable Directive) (a: Int64):
  ∃ rest, e.directivesFromAddress a = e.directivesAtAddress a ++ rest := by
  dsimp [Executable.directivesFromAddress, Executable.directivesAtAddress]
  refine ⟨((e.withAddresses.dropWhile (·.1 ≠ a)).dropWhile (·.1 = a)).map (·.2), ?_⟩
  rw [← List.map_append]
  rw [List.takeWhile_append_dropWhile]

end Kraken


import data.equiv.nat
import computability.encoding
import computability.turing_machine
import data.polynomial.basic
import data.polynomial.eval
import data.finset.basic
-- import measure_theory.measurable_space_def
import .distribution_ensemble

/-!
# UC Protocols

This file defines protocols as they are understood in the 
[Universal Composability Security framework](https://eprint.iacr.org/2000/067.pdf).

-/

-- noncomputable theory

def ste := list bool

structure message := 
(import_tokens : ℕ)
(content : list (bool))

def pair (m1 m2 : message) : message := sorry -- computes a list encoding a pair of lists
def unpair_left (m : message) : message := sorry -- computes the left of a pair encoding
def unpair_right (m : message) : message := sorry -- computes the right of a pair encoding

def encode (n : ℕ) : message := sorry -- encodes a nat as a message
def decode (m : message) : ℕ := sorry -- decodes a nat from a message

inductive incoming_information : Type
| input : incoming_information
| suroutine_output : incoming_information
| backdoor : incoming_information

/-- As defined in section 2.1 -/
structure machine :=
  (ident : ℕ)
  (initial_state : ensemble ste) -- An ensemble of initial states (representing randomness in the machine execution)
  (callers : finset (ℕ)) -- Ids of machines that input to this machine
  (subroutines : finset (ℕ)) -- Ids of machines that give subroutine output to this machine
  (backdoor : finset (ℕ)) -- Ids of machines that backdoor to this machine
  -- given a starting state and a message from ID, return a new state and an outgoing message, or optionally halt
  (program : ste → ℕ → message → option (ste × ℕ × message))
    -- TODO add condition for polytime halting
  (environment_output : option (ste → bool)) 
    -- Optional function for environement machines to run on the environment's state when it halts to determine its output variable

instance : decidable_eq machine := sorry

-- /-- As defined in section 2.1 -/
-- structure protocol :=
--   (ids : finset ℕ)
--   (μ : ℕ → machine)
--   -- ids correspond to ids
--   (ids_match : ∀ i ∈ ids, (μ i).id = i)
--   -- Callers match up with subroutines
--   (callers_have_subroutines : ∀ i j ∈ ids, i ∈ (μ j).callers ↔ j ∈ (μ i).subroutines)

/-- As defined in section 2.1 -/
structure protocol :=
  (machines : finset machine)
  -- Callers match up with subroutines
  (callers_have_subroutines : 
    ∀ (i j : machine), i ∈ machines → i.ident ∈ j.callers ↔ j.ident ∈ i.subroutines)


def protocol.ids (π : protocol) : finset ℕ :=
  π.machines.image machine.ident

/-- 
As defined in section 2.1, the main machines of a protocol are those who have callers whose ids 
are not in the protocol, 
-/
def is_main_machine (π : protocol) (μ : machine) : Prop :=
  μ.ident ∈ π.ids ∧ ∃ m ∈ μ.callers, m ∉ π.ids

-- TODO seems like a bug in the typeclass inference system tha tthis needs to be defined
instance (π : protocol) : decidable_pred (is_main_machine π) := begin
  rw decidable_pred,
  intro a,
  apply and.decidable,
end

/-- 
As defined in section 2.1, the main machines of a protocol are those who have callers whose ids 
are not in the protocol, 
-/
def main_machines (π : protocol) : finset machine :=
  π.machines.filter (is_main_machine π)

/-- ... and the ids of these machines not in the protocol are "external" -/
def external_ids (π : protocol) : finset ℕ := 
  (finset.bUnion (π.machines) (λ μ, μ.callers)) \ π.ids

/-- As defined in 2.2.1 -/
def execution (π : protocol) (𝓐 : machine) (𝓔 : machine) :
  -- (initial_states : ℕ → ste) -- randomness initialization for the machines in the protocol (including input for environment)
  -- (environment_id_zero : 𝓔.id = 0) -- environment machine has id 0
  -- (adversary_id_one : 𝓐.id = 1) -- adversaty machine has id 1
  -- (h0 : 0 ∉ 𝓟.ids) (h1 : 1 ∉ 𝓟.ids) -- 𝓟 does not have 0 or 1 in its id list
  -- (h0' : 0 ∉ external_ids 𝓟) (h1' : 1 ∉ external_ids 𝓟) -- or in its external ids
  ensemble bool := 
sorry

/--  
See definition on page 42. 
An environment is balanced if, at any point in time during the execution, the overall import of
the inputs given to the adversary is at least the sum of the imports of all the other inputs given 
to all the other ITIs in the system so far 
-/
def balanced (𝓔 : machine) : Prop :=
sorry

/-- As defined in 2.2.1 Definition 1 -/
def emulates (π ϕ : protocol) : Prop :=
  ∀ (𝓐 : machine), ∃ (𝓢 : machine), ∀ (𝓔 : machine),
    balanced 𝓔 → (execution π 𝓐 𝓔 ≈ₛ execution π 𝓢 𝓔)

def dummy_machine (ident : ℕ) (forwards_to : ℕ) (callers : finset ℕ) : machine := 
{ ident := ident,
  initial_state := λ n, 
  { val := λ s, if s = [] then 1 else 0, -- todo replace with const added to pmf.lean
    property := 
    begin
      apply has_sum_ite_eq,
    end }, -- doesn't matter, stateless
  callers := callers,
  subroutines := {forwards_to},
  backdoor := ∅,
  program := λ st idx msg, 
    if idx = forwards_to 
      then some ⟨st, decode (unpair_left msg), unpair_right msg⟩
      else some ⟨st, forwards_to, pair msg (encode idx)⟩,
  environment_output := none }

/-- 
Per section 2.2.2, a functionality is described with an ideal protocol which is a protocol with a 
machine for the functionality and a bunch of dummy machines which call the functionality by 
forwarding messages  
-/
def ideal_protocol (m : machine) : protocol :=
{ machines := finset.cons (m : machine) 
    (finset.image (λ i, dummy_machine i m.ident m.callers) m.callers) 
    (by {
      simp only [not_exists, finset.mem_image],
      intros x hx,
      sorry,
    }),
  callers_have_subroutines := sorry }

-- /-- Per section 2.3 -/
-- def subroutine_protocol (𝓟 : protocol) (s : finset ℕ) : protocol :=
-- { ids := 𝓟.ids \ s,
--   μ := 𝓟.μ,
--   ids_match := begin
--     intros i hi,
--     rw finset.mem_sdiff at hi,
--     exact 𝓟.ids_match i hi.left,
--   end,
--   callers_have_subroutines := begin
--     intros i hi j hj,
--     rw finset.mem_sdiff at hi hj,
--     apply 𝓟.callers_have_subroutines,
--     exact hi.left,
--     exact hj.left,
--   end }

/-- Per section 2.3 -/
def subroutine (ϕ π : protocol) : Prop := ϕ.machines ⊆ π.machines

instance : has_subset (protocol) := ⟨λ ϕ π, subroutine ϕ π⟩


/-- Per section 2.3 -/
def compatible (π ϕ : protocol) : Prop :=
∀ μ ∈ π.machines, ∃! μ' ∈ ϕ.machines, ((μ : machine).ident) = (μ'.ident) ∧ μ.callers = μ'.callers
-- Fails without the type ascription, post to forum to figure out whats wrong
-- Is it that lean doesn't know what the type of a member of a list of machines is?
-- I can accept that there might be different has_mem instances for a type, but the infoview
-- indicates it knows μ is a machine

def identity_compatible (π ρ ϕ : protocol) :=
disjoint (π.ids) (ρ.ids \ ϕ.ids)

/-- Per section 2.3 -/
def composed (ρ ϕ π : protocol) (hϕρ : ϕ ⊆ ρ) (hπϕ : compatible π ϕ)
  (h : identity_compatible π ρ ϕ) : protocol :=
{ machines := (ρ.machines \ ϕ.machines) ∪ π.machines,
  callers_have_subroutines := begin
    sorry,
    --follows from compatibility
  end }

/-- Section 2.3 theorem 3 -/
theorem composition_theorem (ρ ϕ π : protocol) (hϕρ : ϕ ⊆ ρ) (hπϕ : compatible π ϕ)
  (h : identity_compatible π ρ ϕ) (h_emulate : emulates π ϕ) :
  emulates (composed ρ ϕ π hϕρ hπϕ h) ρ :=
begin
  sorry,
end
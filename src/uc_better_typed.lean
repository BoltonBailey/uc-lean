

-- TODO: redo the work in uc.lean, but with better conformance to the principles of type theory
-- for example, you might change the indices fron nats to fintypes

-- A Functionality has
-- A type of internal functionality states
-- A number of parties
--    for each party a collection of calls from it to the functionality 
--    a behavior for each of the calls
--    and messages from the functionality to it
-- a distribution on initial states (build the randomness into the initial state?)
-- TODO perhaps it is not best to have calls then call messages, perhaps it's better to just bundle these concepts into one: A party send messages to the functionality (which may implicitly come with a header distinguishing a certain call type)
structure functionality :=
  (states : Type)
  (P : Type*) [P_fin : fintype P] 
  (calls : P → Type) -- for each party an index type of calls
  -- (call_msgs : Π a : P, calls a → Type*) -- for each call, the type for messages
  (behavior : Π p : P, calls p → states → states)




-- A UC Protocol
-- A functionality
-- for each call, a behavior
structure protocol (𝓕 : functionality) :=
  (states : 𝓕.P → Type) -- Internal states for the parties
  (messages : Type)
  (behavior : Π p : 𝓕.P, 𝓕.calls p → states p → (states p × option (𝓕.P × messages)))





-- Define a transcript


-- define UC security


def UC_secure (𝓕 : functionality) (𝓟 : protocol 𝓕) (corrupted : finset 𝓕.P) := 
  ∀ 
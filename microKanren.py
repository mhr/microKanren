# %% [markdown]
# # microKanren
# - Lightly edited version of https://github.com/jtauber/pykanren/blob/master/microkanren.py
# - Major modifications to jtauber's implementation:
#     - `occurs_check` is used in `extend_substitution` now to avoid illegal states
#     - `take_all` actually works with a stream now
#     - `take_all_generator` returns a generator instead of consing a list together
#     - `neq` is a disequality goal constructor
#     - `reify` substitutes every variable in the query's answer (AKA Var(0)) using the substitution

# %%
# LISP-like cons structures

def cons(a, b):
    return (a, b)

def is_cons(c):
    return isinstance(c, tuple) and len(c) == 2

def car(c):
    return c[0]

def cdr(c):
    return c[1]

# helper function for creating nested cons out of lists

def l(*lst):
    if len(lst) == 1:
        return cons(lst[0], ()) # base case is a cons with '()
    else:
        return cons(lst[0], l(*lst[1:]))

class Var:
    """
    (var c) becomes Var(c)
    (var? x) becomes isinstance(x, Var)
    (var=? x_1 x_2) becomes x_1 == x_2
    """
    def __init__(self, index):
        self.index = index

    def __eq__(self, other):
        return isinstance(other, Var) and self.index == other.index

    def __hash__(self):
        return hash(self.index)

    def __repr__(self):
        return "<Var %s>" % self.index

def is_var(v):
    return isinstance(v, Var)

"""
type Substitution = [(Var, Term)]
type State = (Substitution, Counter)

Cons cell representing the current state of the logic program,
consisting of a substitution list and a counter for generating
fresh variables.
"""
EMPTY_STATE = cons({}, 0)

"""
Stream Monad/MonadPlus:

Note that `return` is `unit` in the microKanren code, taking `unit` from category theory (Haskell calls it `return`).

```
data Stream State = MZero | Cons State (Stream State) | Delay (Stream State)
type Goal = State -> Stream State

class Monad m where
    (>>=)  :: m a -> (a -> m b) -> m b
    return :: a -> m a

class Monad m => MonadPlus m where
    mzero :: m a
    mplus :: m a -> m a -> m a

instance Monad (Stream State) where
    (>>=)  :: Stream State -> Goal -> Stream State
    return :: State -> Stream State

instance MonadPlus (Stream State) where
    mzero :: Stream State
    mplus :: Stream State -> Stream State -> Stream State
```
"""

###### Monad ######

def bind(stream, goal):
    """
    (>>=)  :: Stream State -> Goal -> Stream State
    where type Goal = State -> Stream State

    >>= is also known as "bind"
    """
    if stream == mzero:
        # regardless of goal, if stream is unproductive/empty (it's mzero), then the solution stream is mzero
        return mzero
    elif callable(stream):
        # if stream is a thunk, then return a thunk whose body will force the stream/thunk before binding a second time
        return lambda: bind(stream(), goal)
    else:
        # stream is neither empty nor a thunk, so it is productive. pluck off the first solution with car!
        # interleave together (mplus) the following streams:
        # 1) the evaluation of the goal function on the first solution from stream,
        # 2) the binding of the rest of the stream with the goal
        return mplus(goal(car(stream)), bind(cdr(stream), goal))

def unit(state):
    """
    unit :: State -> Stream State

    A function that takes a single State and returns a Stream containing only that State.
    It's akin to the return function in monads, wrapping a value into the monadic context.
    Lifts the State into the Stream monad.
    """
    return cons(state, mzero)

###### MonadPlus ######

"""
mzero :: Stream State

Represents an empty stream of states.
It's equivalent to an empty list in Haskell and acts as the identity element for the mplus operation.
"""
mzero = ()

def mplus(stream1, stream2):
    """
    mplus :: Stream State -> Stream State -> Stream State

    Interleave streams inside thunks that force thunks, building up solution list
    """
    if stream1 == mzero:
        # if stream1 is unproductive/empty (it's mzero) then
        # return stream2 (because stream2 contains all the solutions that remain)
        return stream2
    elif callable(stream1):
        # if stream1 is a thunk then
        # return a thunk that interleaves stream2 with forced stream1 thunk (swapping order, resulting in the interleaving)
        return lambda: mplus(stream2, stream1())
    else:
        # stream1 is neither empty nor a thunk, so it is productive. pluck off the first solution with car!
        # construct a new list with the first solution from stream1 and the interleaved stream of [the rest of stream1] with stream2
        return cons(car(stream1), mplus(cdr(stream1), stream2))

##### Control flow expressed in terms of the Stream monad #####

def walk(u, s):
    """
    walk :: Var -> Substitution -> Term
    
    Recursively walk down a substitution dictionary s for an assignment of the term u to a value,
    if u is a variable.
    """
    if is_var(u):
        if u in s:
            a = s[u]
            return walk(a, s)
        else:
            return u
    else:
        return u

def occurs_check(var, value, s):
    """
    occurs_check :: Var -> Term -> Substitution -> Bool

    Check for circular references in substitution s to prevent infinite loops.
    """
    value = walk(value, s)  # Walk value through the substitutions to get its assignment
    if var == value:
        return True
    else:
        return is_cons(value) and (occurs_check(var, car(value), s) or
                                   occurs_check(var, cdr(value), s))

def extend_substitution(x, v, s):
    """
    extend_substitution :: Var -> Term -> Substitution -> Maybe Substitution
    
    Extend the substitution dictionary s with a new
    variable-term binding (variable x -> value v),
    if no circular reference is detected (occurs-check).
    """
    if occurs_check(x, v, s):
        # fail if x occurs in v, preventing circular references
        return False
    # copy because we are about to mutate the substitution dict s
    s = s.copy()
    s[x] = v
    return s

def unify(u, v, s):
    """
    unify :: Term -> Term -> Substitution -> Maybe Substitution

    Unify two terms under a given substitution dictionary s.
    """
    u = walk(u, s)
    v = walk(v, s)
    if is_var(u) and is_var(v) and u == v:
        return s
    elif is_var(u):
        return extend_substitution(u, v, s)
    elif is_var(v):
        return extend_substitution(v, u, s)
    elif is_cons(u) and is_cons(v):
        s = unify(car(u), car(v), s)
        t = unify(cdr(u), cdr(v), s)
        return t if t is not False else s
    else:
        return u == v and s

def eq(u, v):
    """
    eq :: Term -> Term -> Goal

    A goal constructor that takes two terms and returns a goal that
    attempts to unify u and v, applying unit to the new state of
    unification (new substitution with old counter), otherwise
    returning mzero if the unification failed.
    """
    def goal(state):
        new_state = unify(u, v, car(state))
        if new_state is not False:
            return unit(cons(new_state, cdr(state)))
        else:
            return mzero

    return goal

def neq(u, v):
    """
    neq :: Term -> Term -> Goal

    A goal constructor that takes two terms and returns a goal that
    attempts to unify u and v, applying unit to the new state of unification
    (old substitution with old counter since the point is that they don't unify),
    otherwise returning mzero if the unification succeeded.
    """
    def goal(state):
        new_state = unify(u, v, car(state))
        if new_state is False:
            return unit(state) # return state unchanged
        else:
            # if unify succeeds, it means u and v can be made equal, which contradicts the neq goal
            # hence, neq should fail, represented by mzero
            return mzero
    return goal

def call_fresh(f):
    """
    call_fresh :: (Var -> Goal) -> Goal

    Introduces a fresh logic variable and constructs a goal with it.
    """
    def goal(state):
        c = cdr(state)
        return f(Var(c))(cons(car(state), c + 1))

    return goal

def disj(goal1, goal2):
    """
    disj :: Goal -> Goal -> Goal

    Represents logical disjunction (OR) of two goals,
    using mplus to interleave the streams that come from evaluating the goals.
    """
    def goal(state):
        return mplus(goal1(state), goal2(state))
    return goal

def conj(goal1, goal2):
    """
    conj :: Goal -> Goal -> Goal

    Represents logical conjunction (AND) of two goals,
    using bind (which uses mplus to interleave) to evaluate each goal in sequence.
    """
    def goal(state):
        return bind(goal1(state), goal2)
    return goal

##### Running goal queries to get results #####

def pull(stream):
    """
    pull :: Stream -> Stream

    - If stream is a thunk, call it and pass its result to pull.
    - If stream is otherwise, like a productive cons or an unproductive mzero,
    then return it.
    """
    if callable(stream):
        return pull(stream())
    else:
        return stream
    
def take(n, stream):
    """
    take :: Int -> Stream -> [Substitution]
    where type Substitution = [(Var, Term)]

    Recursively force streams, constructing a list of first solution
    and take'd rest of the stream, decrementing until we hit base
    case of n == 0.
    """
    if n == 0:
        return ()
    else:
        stream = pull(stream)
        if stream == mzero:
            return ()
        else:
            return cons(car(stream), take(n - 1, cdr(stream)))

def take_all(stream):
    """
    take_all :: Stream -> [Substitution]
    where type Substitution = [(Var, Term)]

    Recursively force streams, constructing a list of first solution
    and take'd rest of the stream, until we hit base case of empty.
    """
    stream = pull(stream)
    if stream == mzero:
        return ()
    else:
        return cons(car(stream), take_all(cdr(stream)))

def take_all_generator(stream):
    """
    Similar to take_all, except yielding elements in a generator
    instead of constructing a list.
    """
    stream = pull(stream)
    if stream == mzero:  # Use mzero to check for the end of the stream
        return
    else:
        yield car(stream)
        # iteratively return every element in the generator returned from
        # the recursive take_all_generator call
        yield from take_all_generator(cdr(stream))

def run(query, n=None):
    """
    run :: ([Var] -> Goal) -> Maybe Int -> [Substitution]
    where type Substitution = [(Var, Term)]
    
    Combines run* and run from original microKanren.
    Executes a logic program, returning a specified number of solutions
    or all solutions, where a solution is a substitution satisfying all the goals,
    depending on if n (Maybe Int) is Int or None.
    """
    def run_generator():
        gen = take_all_generator(query(EMPTY_STATE))
        count = 0
        for item in gen:
            if n is not None and count >= n:
                break
            yield item
            count += 1
        if n is not None and count < n:
            raise RuntimeError("Requested more solutions than are available.")

    return list(run_generator())

def reify(v, s):
    """
    reify :: Term -> Substitution -> Term
    where type Term = Var | Literal | (Term, Term)
          type Substitution = [(Var, Term)]

    - v: The current value to reify, which could be a variable,
    a literal, or a cons cell.
    - s: substitution dictionary containing variable bindings,
    { var: term }

    From recursively walking, we obtain the reified value with
    variables replaced by their literals (where possible).
    """
    if is_var(v):
        # v is a variable, so walk the substitution to get its value
        value = walk(v, s)
        if is_var(value):
            # value is a free variable despite walking, so we're done
            return value
        else:
            # value is not a variable after walking, so it might need further reification
            return reify(value, s)
    elif is_cons(v):
        # v is a cons cell: recursively reify its head and tail
        head, tail = v
        return (reify(head, s), reify(tail, s))
    else:
        # v is a literal (including the empty tuple, ())
        return v

if __name__ == "__main__":
    s1 = {Var(0): 5, Var(1): True}
    s2 = {Var(1): 5, Var(0): Var(1)}

    assert walk(Var(0), s1) == 5
    assert walk(Var(0), s2) == 5

    assert unify(None, 1, {}) is False
    assert unify(None, Var(0), {}) == {Var(0): None}
    assert unify(None, [1, Var(0)], {}) is False
    assert unify(1, None, {}) is False
    assert unify(1, 1, {}) == {}
    assert unify(1, 2, {}) is False
    assert unify(1, Var(0), {}) == {Var(0): 1}
    assert unify(1, [], {}) is False
    assert unify(Var(0), 1, {}) == {Var(0): 1}
    assert unify(Var(0), Var(1), {}) == {Var(0): Var(1)}
    assert unify(Var(0), [], {}) == {Var(0): []}
    assert unify(Var(0), l(1, 2, 3), {}) == {Var(0): l(1, 2, 3)}
    assert unify(l(1, 2, 3), l(1, 2, 3), {}) == {}
    assert unify(l(1, 2, 3), l(3, 2, 1), {}) is False
    assert unify(l(Var(0), Var(1)), l(1, 2), {}) == {Var(0): 1, Var(1): 2}
    assert unify(l(l(1, 2), l(3, 4)), l(l(1, 2), l(3, 4)), {}) == {}
    assert unify(l(l(Var(0), 2), l(3, 4)), l(l(1, 2), l(3, 4)), {}) == {Var(0): 1}

    assert unify((1, (2, (3, 4))), (1, (2, Var(0))), {}) == {Var(0): (3, 4)}

    assert unify({}, {}, {}) == {}

    assert eq(1, 1)(EMPTY_STATE) == (EMPTY_STATE, ())
    assert eq(1, 2)(EMPTY_STATE) == ()

    assert take(0, l(1, 2, 3)) == ()
    assert take(1, l(1, 2, 3)) == (1, ())
    assert take(2, l(1, 2, 3)) == (1, (2, ()))
    assert take(3, l(1, 2, 3)) == (1, (2, (3, ())))
            
    # microKanren test programs

    a_and_b = call_fresh(lambda a:
                         call_fresh(lambda b:
                                    conj(
                                        eq(a, 7),
                                        disj(eq(b, 5), eq(b, 6)))))

    def fives(x):
        return disj(
            eq(x, 5),
            lambda a_c: lambda: fives(x)(a_c)
        )
    
    def appendo(l, s, out):
        return call_fresh(lambda a: call_fresh(lambda d: call_fresh(lambda res:
            disj(
                # Base case: if l is empty, then out must be equal to s
                conj(eq((), l), eq(s, out)),
                # Recursive case
                conj(
                    eq(cons(a, d), l),
                    conj(
                        eq(cons(a, res), out),
                        lambda state:
                            lambda:
                                appendo(d, s, res)(state)))))))

    # microKanren tests

    # second-set t1
    assert car(call_fresh(lambda q: eq(q, 5))(EMPTY_STATE)) == ({Var(0): 5}, 1)

    # second-set t2
    assert cdr(call_fresh(lambda q: eq(q, 5))(EMPTY_STATE)) == mzero

    # second-set t3
    assert car(a_and_b(EMPTY_STATE)) == ({Var(0): 7, Var(1): 5}, 2)

    # run - take first element of a single-element list
    assert run(a_and_b, n=1)[0] == ({Var(0): 7, Var(1): 5}, 2)

    # second-set t3, take
    assert take(1, a_and_b(EMPTY_STATE)) == (({Var(0): 7, Var(1): 5}, 2), mzero)

    # second-set t4
    assert car(cdr(a_and_b(EMPTY_STATE))) == ({Var(0): 7, Var(1): 6}, 2)

    # second-set t5
    assert cdr(cdr(a_and_b(EMPTY_STATE))) == mzero

    # take 1 call_fresh with fives
    assert take(1, call_fresh(lambda q: fives(q))(EMPTY_STATE)) == (({Var(0): 5}, 1), mzero)

    # take 2 a-and-b stream
    assert take(2, a_and_b(EMPTY_STATE)) == (({Var(0): 7, Var(1): 5}, 2), (({Var(0): 7, Var(1): 6}, 2), mzero))

    # take-all a-and-b stream
    assert take_all(a_and_b(EMPTY_STATE)) == (({Var(0): 7, Var(1): 5}, 2), (({Var(0): 7, Var(1): 6}, 2), mzero))

    # infinite stream
    for solution in take_all_generator(call_fresh(fives)(EMPTY_STATE)):
        assert solution == ({Var(0): 5}, 1)
        break

    # disequality
    def goal_neq_ab(state):
        def not_equal_goal(a, b):
            return conj(
                eq(a, 6),
                conj(
                    eq(b, 5),
                    neq(a, b)
                )
            )

        return call_fresh(lambda a: call_fresh(lambda b:
                                               not_equal_goal(a, b)))(state)

    assert run(goal_neq_ab,
            n=1
            #   n=2 # raises an error
            ) == [({Var(0): 6, Var(1): 5}, 2)]
    
    # appendo test

    list1 = l(1, 2)
    list2 = l(3, 4)

    def res_query(list1, list2, result):
        return appendo(list1, list2, result)
        
    # result = run(call_fresh(lambda res: res_query(list1, list2, res)), n=1)
    
    result = run(call_fresh(lambda res: res_query(list1, list2, res)))

    for res in result:
        subst, _ = res
        answer = subst[Var(0)]
        print(reify(answer, subst))
        assert reify(answer, subst) == l(1, 2, 3, 4)

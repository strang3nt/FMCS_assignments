import pynusmv
import sys
from pynusmv_lower_interface.nusmv.parser import parser 
from collections import deque
from itertools import takewhile 

specTypes = {'LTLSPEC': parser.TOK_LTLSPEC, 'CONTEXT': parser.CONTEXT,
    'IMPLIES': parser.IMPLIES, 'IFF': parser.IFF, 'OR': parser.OR, 'XOR': parser.XOR, 'XNOR': parser.XNOR,
    'AND': parser.AND, 'NOT': parser.NOT, 'ATOM': parser.ATOM, 'NUMBER': parser.NUMBER, 'DOT': parser.DOT,

    'NEXT': parser.OP_NEXT, 'OP_GLOBAL': parser.OP_GLOBAL, 'OP_FUTURE': parser.OP_FUTURE,
    'UNTIL': parser.UNTIL,
    'EQUAL': parser.EQUAL, 'NOTEQUAL': parser.NOTEQUAL, 'LT': parser.LT, 'GT': parser.GT,
    'LE': parser.LE, 'GE': parser.GE, 'TRUE': parser.TRUEEXP, 'FALSE': parser.FALSEEXP
}

basicTypes = {parser.ATOM, parser.NUMBER, parser.TRUEEXP, parser.FALSEEXP, parser.DOT,
              parser.EQUAL, parser.NOTEQUAL, parser.LT, parser.GT, parser.LE, parser.GE}
booleanOp = {parser.AND, parser.OR, parser.XOR, parser.XNOR, parser.IMPLIES, parser.IFF}

def spec_to_bdd(model, spec):
    """
    Given a formula `spec` with no temporal operators, returns a BDD equivalent to
    the formula, that is, a BDD that contains all the states of `model` that
    satisfy `spec`
    """
    bddspec = pynusmv.mc.eval_simple_expression(model, str(spec))
    return bddspec
    
def is_boolean_formula(spec):
    """
    Given a formula `spec`, checks if the formula is a boolean combination of base
    formulas with no temporal operators. 
    """
    if spec.type in basicTypes:
        return True
    if spec.type == specTypes['NOT']:
        return is_boolean_formula(spec.car)
    if spec.type in booleanOp:
        return is_boolean_formula(spec.car) and is_boolean_formula(spec.cdr)
    return False
    
def check_GF_formula(spec):
    """
    Given a formula `spec` checks if the formula is of the form GF f, where f is a 
    boolean combination of base formulas with no temporal operators.
    Returns the formula f if `spec` is in the correct form, None otherwise 
    """
    # check if formula is of type GF f_i
    if spec.type != specTypes['OP_GLOBAL']:
        return False
    spec = spec.car
    if spec.type != specTypes['OP_FUTURE']:
        return False
    if is_boolean_formula(spec.car):
        return spec.car
    else:
        return None

def parse_react(spec):
    """
    Visit the syntactic tree of the formula `spec` to check if it is a reactive formula,
    that is wether the formula is of the form
    
                    GF f -> GF g
    
    where f and g are boolean combination of basic formulas.
    
    If `spec` is a reactive formula, the result is a pair where the first element is the 
    formula f and the second element is the formula g. If `spec` is not a reactive 
    formula, then the result is None.
    """
    # the root of a spec should be of type CONTEXT
    if spec.type != specTypes['CONTEXT']:
        return None
    # the right child of a context is the main formula
    spec = spec.cdr
    # the root of a reactive formula should be of type IMPLIES
    if spec.type != specTypes['IMPLIES']:
        return None
    # Check if lhs of the implication is a GF formula
    f_formula = check_GF_formula(spec.car)
    if f_formula == None:
        return None
    # Create the rhs of the implication is a GF formula
    g_formula = check_GF_formula(spec.cdr)
    if g_formula == None:
        return None
    return (f_formula, g_formula)

def compute_reach(model):
    reach = model.init
    new = model.init
    trace = []
    while new.isnot_false():
        trace = trace + [new]
        new = model.post(new) - reach
        reach = reach + new
    return reach, trace

def find_cycle_start(model, recur, pre_reach):
    s = model.pick_one_state(recur)
    while True:
        r = pynusmv.dd.BDD.false()
        new = model.post(s) & pre_reach
        cycle_trace = [new]
        while new.isnot_false():
            r = r + new
            new = (model.post(new) & pre_reach) - r
            cycle_trace.append(new)
        r = r & recur
        if s.entailed(r):
            return s, cycle_trace
        else:
            s = model.pick_one_state(r)

def build_cycle(model, s, cycle_trace):
    path = [model.pick_one_inputs(s)] + [s]
    curr = s

    for new_i in reversed(list(takewhile(lambda x: not(s.entailed(x)), cycle_trace))):
        pred = model.pre(curr) & new_i
        curr = model.pick_one_state(pred)
        path = [model.pick_one_inputs(curr)] + [curr] + path # insert to head
        
    return [s] + path

def generate_witness(model, trace, final_states):
    """
    final_states is the state that starts the loop.
    Generation of witness should start from init and finish from the previous element of trace s.t. trace[i] contains final_states.
    """
    state = model.pick_one_state(final_states & trace[-1])
    if len(trace) == 1: return [state]
    return generate_witness(
        model, 
        trace[:-1], 
        model.pre(final_states)) + [model.pick_one_inputs(state), state]

def symbolic_repeatable(model, f, not_g):
    reach, trace = compute_reach(model)

    recur = reach & f & not_g
    while recur.isnot_false():
        pre_reach = pynusmv.dd.BDD.false() # empty BDD
        new = model.pre(recur) & not_g
        
        while new.isnot_false():
            pre_reach = pre_reach + new
            if recur.entailed(pre_reach):
                s, cycle_trace = find_cycle_start(model, recur, pre_reach)
                first_trace = generate_witness(
                    model, 
                    list(takewhile(lambda x: not(s.entailed(x)), trace)) + [s], 
                    s
                )
                return True, first_trace[:-1] + list(build_cycle(model, s, cycle_trace))
                
            new = (model.pre(new) - pre_reach) & not_g
        recur = recur & pre_reach # removes states that cannot form loop
    return False, None

def check_react_spec(spec):
    """
    Return whether the loaded SMV model satisfies or not the GR(1) formula
    `spec`, that is, whether all executions of the model satisfies `spec`
    or not. 
    """
    spec_parsed = parse_react(spec) 
    if spec_parsed == None:
        return None
    f, g = spec_parsed

    model = pynusmv.glob.prop_database().master.bddFsm
    res, trace = symbolic_repeatable(model, spec_to_bdd(model, f) ,spec_to_bdd(model, ~g))
    return not res, tuple(map(lambda var: var.get_str_values(), trace)) if res else None
    
if len(sys.argv) != 2:
    print("Usage:", sys.argv[0], "filename.smv")
    sys.exit(1)

pynusmv.init.init_nusmv()
filename = sys.argv[1]
pynusmv.glob.load_from_file(filename)
pynusmv.glob.compute_model()
type_ltl = pynusmv.prop.propTypes['LTL']
for prop in pynusmv.glob.prop_database():
    spec = prop.expr
    print(spec)
    if prop.type != type_ltl:
        print("property is not LTLSPEC, skipping")
        continue
    res = check_react_spec(spec)
    if res == None:
        print('Property is not a GR(1) formula, skipping')
    if res[0] == True:
        print("Property is respected")
    elif res[0] == False:
        print("Property is not respected")
        print("Counterexample:", res[1])

pynusmv.init.deinit_nusmv()

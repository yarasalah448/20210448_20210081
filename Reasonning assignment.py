import string
from random import random
from sympy import symbols, Function
from sympy import symbols, And, Or, simplify, sympify

from numpy.random.mtrand import rand

x, y = symbols('x y')
f = Function('f')


def Eliminate_implication(phrase):
    print(phrase)
    phrase.replace("->", "&~")
    print(phrase)
    return phrase.replace("->", "&~")


print(Eliminate_implication("∀x∀y∀z(M(x)->~M(y)&~M(z))"))
a = "ayaayaya"
print(a.replace("ay", "g"))


def find_closing_bracket_index(phrase, open_index):
    stack = []
    for i, char in enumerate(phrase):
        if char == '(':
            stack.append(i)
        elif char == ')':
            if stack[-1] == open_index:
                return i
            stack.pop()
    return -1  # If no corresponding closing bracket is found


def De_morgans_law(phrase):
    for i in range(len(phrase) - 1):
        if phrase[i] == '~' and phrase[i + 1] == '(':
            phrase_1 = phrase[:i] + phrase[i + 1:]
            c_index = find_closing_bracket_index(phrase_1, i)
            sub_phrase = phrase_1[i:c_index + 1]
            sub_phrase = list(sub_phrase)  # Convert string to a list
            for j in range(len(sub_phrase)):
                if sub_phrase[j] == '&':
                    sub_phrase = sub_phrase[:j] + ["|", "~"] + sub_phrase[j + 1:]
                    break
                elif sub_phrase[j] == '|':
                    sub_phrase = sub_phrase[:j] + ["&", "~"] + sub_phrase[j + 1:]
                    break
                elif j == 0:
                    sub_phrase = ["(", "~"] + sub_phrase[1:]
            for j in range(len(sub_phrase)):
                if sub_phrase[j] == '~' and sub_phrase[j + 1] == '∃':
                    sub_phrase[j + 1] = '∀'
                    sub_phrase.pop(j)
                    sub_phrase.insert(j + 2, "~")
                elif sub_phrase[j] == '~' and sub_phrase[j + 1] == '∀':
                    sub_phrase[j + 1] = '∃'
                    sub_phrase.pop(j)
                    sub_phrase.insert(j + 2, "~")
            sub_phrase = ''.join(sub_phrase)
            phrase = phrase_1[:i] + sub_phrase + phrase_1[c_index + 1:]
    return phrase


k = De_morgans_law("~(f(x)&∃xg(x))")
print(k)

import random
import string


def Remove_double_negation(phrase):
    return phrase.replace("~~", "")


def random_letter(li):
    rand_l = random.choice(string.ascii_letters)
    if rand_l not in li:
        return rand_l
    return random_letter(li)


def Standardize_variables(phrase):
    stack = []
    phrase = list(phrase)  # Convert to list
    for i in range(len(phrase)):
        if phrase[i] == '(':
            indx = find_closing_bracket_index(phrase, i)
            if indx - i == 2:
                val = phrase[i + 1]
                if len(stack) == 0:
                    stack.append(val)
                else:
                    if val in stack:
                        val = random_letter(stack)
                        phrase[i + 1] = val
                    else:
                        stack.append(val)
                if phrase[i - 3] == '∀' or phrase[i - 3] == '∃':
                    phrase[i - 2] = val
    return ''.join(phrase)  # Convert back to string


o = Standardize_variables("(∀xP(x))∨(∃xQ(x))")
print(o)


def Turn_conjunctions(phrase):
    li = phrase.split('&')
    return li


def prenix_phrase1(phrase):
    existential_quantifiers = []
    rest_of_phrase = ""

    i = 0
    while i < len(phrase):
        if phrase[i] == '∃':
            j = i + 1
            while j < len(phrase) and phrase[j] != ' ':
                j += 1
            existential_quantifiers.append(phrase[i:j])

            phrase = phrase[:i] + phrase[j:]
        else:

            i += 1

    reorganized_phrase = ' '.join(existential_quantifiers) + ' ' + phrase.strip()

    return reorganized_phrase
##############################################
def prenix_phrase2(phrase):
    universal_quantifiers = []
    rest_of_phrase = ""
    i = 0
    while i < len(phrase):
        if phrase[i] == '∀':
            j = i + 1
            while j < len(phrase) and phrase[j] != ' ':
                j += 1
            universal_quantifiers.append(phrase[i:j])

            phrase = phrase[:i] + phrase[j:]
        else:

            i += 1

        reorganized_phrase = ' '.join(universal_quantifiers) + ' ' + phrase.strip()

    return reorganized_phrase.replace(" ", "")


phrase = "(∀x P(x)) ∨ (∃y Q(y))"
prenix1 = prenix_phrase1(phrase)
prenix2 = prenix_phrase2(prenix1)
print(prenix2)


def eliminate_existential_quantifiers(expression):
    # sympify(expression).args
    skolem_function = Function('f')
    for subexpr in sympify(expression).args:
        if subexpr.is_Exists:
            bound_vars = subexpr.variables
            skolem_args = [symbols(f"{var.name}_{i}") for i, var in enumerate(bound_vars)]
            skolem_expr = skolem_function(*skolem_args)
            expression = expression.subs(subexpr, skolem_expr)
    return expression


def eliminate_universal_quantifiers(expression):
    modified_expression = expression
    for subexpr in expression.args:
        if subexpr.is_ForAll:
            modified_expression = modified_expression.subs(subexpr, subexpr.expr)
    return modified_expression


def distributiveLaws(expression):
    
    if isinstance(expression, Or):
        if isinstance(expression.args[0], And):
            and_expr = expression.args[0]
            other_expr = Or(*expression.args[1:])
            distributed_expr = And(*[Or(arg, other_expr) for arg in and_expr.args])
            return distributiveLaws(distributed_expr)
        elif isinstance(expression.args[1], And):
            and_expr = expression.args[1]
            other_expr = Or(*expression.args[0:])
            distributed_expr = And(*[Or(other_expr, arg) for arg in and_expr.args])
            return distributiveLaws(distributed_expr)
        else:
            return Or(*(distributiveLaws(arg) for arg in expression.args))
    elif isinstance(expression, And):
        return And(*(distributiveLaws(arg) for arg in expression.args))
    else:
        return expression


li = ["∀x(T(x)->~M(x))"
    , "∀x∀y∀z(M(x)->~M(y)&~M(z))"
    , "T(Arthur)->M(Carleton)"
    , "T(Bertram)->~M(Bertram)"
    , "T(Carleton)->~M(Carleton)"
    , "T(Arthur)"
    , "T(Bertram)"]
print("-------------------------------")
for i in range(len(li)):
    li[i] = Eliminate_implication(li[i])
    li[i] = De_morgans_law(li[i])
    li[i] = Remove_double_negation(li[i])
    li[i] = Standardize_variables(li[i])
    li[i] = prenix_phrase2(li[i])
    # li[i] = eliminate_existential_quantifiers(li[i])
    # li[i] = eliminate_universal_quantifiers(li[i])
    # li[i] = distributiveLaws(li[i])

print(distributiveLaws("(M(x)Or(~M(y)AndM(z)))"))
# print(li)

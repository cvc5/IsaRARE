# SMT in Isabelle/HOL

Formalization of [SMT-LIB Theories](https://smtlib.cs.uiowa.edu/theories.shtml) in Isabelle/HOL.

## Supported SMT-LIB Functions

Currently, only the [Core](https://smtlib.cs.uiowa.edu/theories-Core.shtml) and the [String](https://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml) theory are available.

### Core

| Function               |     |
| ---------------------- | --- |
| `(true Bool)`          | ✅*  |
| `(false Bool)`         | ✅*  |
| `(not Bool Bool)`      | ✅*  |
| `(=> Bool Bool Bool)`  | ✅*  |
| `(and Bool Bool Bool)` | ✅*  |
| `(or Bool Bool Bool)`  | ✅*  |
| `(xor Bool Bool Bool)` | ❌   |
| `(= A A Bool)`         | ✅*  |
| `(distinct A A Bool)`  | ❌   |
| `(ite Bool A A A)`     | ✅   |

*Shallow embedding in Isabelle

### Strings

| Function                                           |     |
| -------------------------------------------------- | --- |
| `(str.++ String String String)`                    | ✅   |
| `(str.len String Int)`                             | ✅   |
| `(str.< String String Bool)`                       | ✅   |
| `(str.to_re String RegLan)`                        | ✅   |
| `(str.in_re String RegLan Bool)`                   | ✅   |
| `(re.none RegLan)`                                 | ✅   |
| `(re.all RegLan)`                                  | ✅   |
| `(re.allchar RegLan)`                              | ✅   |
| `(re.++ RegLan RegLan RegLan)`                     | ✅   |
| `(re.union RegLan RegLan RegLan)`                  | ✅   |
| `(re.inter RegLan RegLan RegLan)`                  | ✅   |
| `(re.* RegLan RegLan)`                             | ✅   |
| `(str.<= String String Bool :chainable)`           | ✅   |
| `(str.at String Int String)`                       | ✅   |
| `(str.substr String Int Int String)`               | ✅   |
| `(str.prefixof String String Bool)`                | ✅   |
| `(str.suffixof String String Bool)`                | ✅   |
| `(str.contains String String Bool)`                | ✅   |
| `(str.indexof String String Int Int)`              | ✅   |
| `(str.replace String String String String)`        | ✅   |
| `(str.replace_all String String String String)`    | ❌   |
| `(str.replace_re String RegLan String String)`     | ❌   |
| `(str.replace_re_all String RegLan String String)` | ❌   |
| `(re.comp RegLan RegLan)`                          | ✅   |
| `(re.diff RegLan RegLan RegLan)`                   | ✅   |
| `(re.+ RegLan RegLan)`                             | ✅   |
| `(re.opt RegLan RegLan)`                           | ✅   |
| `(re.range String String RegLan)`                  | ✅   |
| `((_ re.^ n) RegLan RegLan)`                       | ✅   |
| `((_ re.loop n₁ n₂) RegLan RegLan)`                | ✅   |
| `(str.is_digit String Bool)`                       | ✅   |
| `(str.to_code String Int)`                         | ✅   |
| `(str.from_code Int String)`                       | ✅   |
| `(str.to_int String Int)`                          | ✅   |
| `(str.from_int Int String)`                        | ✅   |

## File Structure

- `Core.thy`: Implementation of the [SMT-LIB core theory](https://smtlib.cs.uiowa.edu/theories-Core.shtml)
- `Strings.thy`: Implementation of the quantifier-free [SMT-LIB string theory](https://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml)
- `string/`:
  - `Words.thy`: Formalization of words (= strings)
  - `Regular.thy`: Formalization of regular languages including language derivatives
  - `RegEx.thy`: Formalization of regular expression including regex-derivatives
- `spec.json`: Contains the specification to convert SMT-LIB syntax to the syntax of the Isabelle theories

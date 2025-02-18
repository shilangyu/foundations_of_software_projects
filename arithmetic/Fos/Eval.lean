import Fos.Term
import Fos.Reduce
namespace Fos

inductive EvalResult where
| Ok : Term -> EvalResult
| Error : EvalResult
open EvalResult

@[simp]
def eval : Term -> EvalResult
  | Term.t_true => Ok Term.t_true
  | Term.t_false => Ok Term.t_false
  | Term.t_zero => Ok Term.t_zero
  | Term.t_if t1 t2 t3 => match eval t1 with
    | Ok Term.t_true => eval t2
    | Ok Term.t_false => eval t3
    | _ => Error
  | Term.t_succ t1 => match eval t1 with
    | Ok t1' => Ok (Term.t_succ t1')
    | _ => Error
  | Term.t_pred t1 => match eval t1 with
    | Ok Term.t_zero => Ok Term.t_zero
    | Ok (Term.t_succ nv) => Ok nv
    | _ => Error
  | Term.t_iszero t1 => match eval t1 with
    | Ok Term.t_zero => Ok Term.t_true
    | Ok (Term.t_succ _) => Ok Term.t_false
    | _ => Error


namespace Example

#reduce eval example1
#reduce eval example2
#reduce eval (isGreaterThanTwo one)
#reduce eval (isGreaterThanTwo two)
#reduce eval (isGreaterThanTwo three)

end Example

end Fos

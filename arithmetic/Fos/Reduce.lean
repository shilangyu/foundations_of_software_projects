import Fos.Term
namespace Fos

inductive ReduceResult where
| Reduced : Term -> ReduceResult
| NotReducible : ReduceResult
open ReduceResult

def reduce : Term -> ReduceResult
  | Term.t_if #t t1 _ => Reduced t1
  | Term.t_if #f _ t2 => Reduced t2
  | Term.t_iszero #0 => Reduced #t
  | Term.t_iszero (Term.t_succ t) => if isNumericalVal t then Reduced #f else NotReducible
  | Term.t_pred #0 => Reduced #0
  | Term.t_pred (Term.t_succ t) => if isNumericalVal t then Reduced t else NotReducible
  | Term.t_if t1 t2 t3 => match reduce t1 with
    | Reduced t1' => Reduced (Term.t_if t1' t2 t3)
    | NotReducible => NotReducible
  | Term.t_iszero t => match reduce t with
    | Reduced t' => Reduced (Term.t_iszero t')
    | NotReducible => NotReducible
  | Term.t_pred t => match reduce t with
    | Reduced t' => Reduced (Term.t_pred t')
    | NotReducible => NotReducible
  | Term.t_succ t => match reduce t with
    | Reduced t' => Reduced (Term.t_succ t')
    | NotReducible => NotReducible
  | #0 | #t | #f => NotReducible

namespace Example

def example1 :=
#if #t #then #0 #else succ #0

#reduce example1
#reduce reduce example1

def one := succ #0
def two := succ one
def three := succ two

def example2 :=
#if iszero? (pred (pred (pred three))) #then #t #else #f

#reduce example2
#reduce reduce example2


def isGreaterThanTwo (t : Term) : Term :=
#if iszero? t #then #f #else
#if iszero? (pred t) #then #f #else
#if iszero? (pred (pred t)) #then #f #else #t

#reduce isGreaterThanTwo three
#reduce reduce (isGreaterThanTwo three)

end Example

end Fos

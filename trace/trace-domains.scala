package pllab.lwnn.abstract_domains

import pllab.lwnn.syntax._
import Pretty.{ stmt2str ⇒ pretty }
import scala.collection.mutable.LinkedHashSet
import scala.collection.mutable.Stack

// DEFINES THE FOLLOWING SEMANTIC DOMAINS
//
//  t  ∈ Term = Decl + Stmt + Value          | terms
//  ρ  ∈ Env = Variable → Address            | abstract environments
//  σ  ∈ Store = Address → Value             | abstract stores
//  a  ∈ Address = Label (an integer)        | abstract addresses
//  v  ∈ Value = ℤ# x Set of Closures                         | abstract values
//  n  ∈ ℤ#                                  | abstract integers
//  κ  ∈ Kont                                | semantic continuations

// terms (conflating decl and stmt)
sealed abstract class Term
case class StmtT(s: Stmt) extends Term
case class ValueT(v: Value) extends Term

// environment
case class Env(ρ: Map[Var, Address] = Map()) {

  // retrieve a variable's address
  def apply(x: Var): Address =
    ρ get x match {
      case Some(a) ⇒ a
      case None ⇒ sys.error("undefined")
    }

  // add bindings to the environment
  def ++(bindings: List[(Var, Address)]): Env =
    Env(ρ ++ bindings)

  // filter mapping
  def filter(f: Var => Boolean): Env =
    Env(ρ filterKeys f)

}

package object Counter {
  var ctr: Map[Address, Int] = Map();
  var k:Int = 1
}

// store 
case class Store(sto: Map[Address, AbstractValue] = Map()) {

  // lattice join: for each address, join the corresponding values in
  // each store. the domains of the two stores should be identical.
  def ⊔(σ: Store): Store = {
    assert(sto.keys == σ.sto.keys)
    val sto1 = sto.keys.foldLeft(Map[Address, AbstractValue]())(
      (acc, a) ⇒ acc + (a → (sto(a) ⊔ σ.sto(a))))
    Store(sto1)
  }

  // widening operator
  def ▽(σ: Store): Store = {    
    val sto1 = sto.keys.foldLeft(Map[Address, AbstractValue]())(
      (acc, a) ⇒ {
        if (!sto.contains(a)) {
          acc + (a → (σ.sto(a)))
        } else if (!σ.sto.contains(a)) {
          acc + (a → (sto(a)))
        } else {
          acc + (a → (sto(a) ▽ σ.sto(a)))
        }
      })

    val sto2 = σ.sto.keys.foldLeft(Map[Address, AbstractValue]())(
      (acc, a) ⇒ {
        if (!sto.contains(a)) {
          acc + (a → (σ.sto(a)))
        } else if (!σ.sto.contains(a)) {
          acc + (a → (sto(a)))
        } else {
          acc + (a → (sto(a) ▽ σ.sto(a)))
        }
      })

    Store(sto1 ++ sto2)
  }

  // retrieve an address' value
  def apply(a: Address): AbstractValue =
    sto get a match {
      case Some(v) ⇒ v
      case None ⇒ {
        sys.error(a + " is inconceivable. Value = ")
      }
    }

  // add a value to the store at the given address
  def +(av: (Address, AbstractValue)): Store = {
    if (Counter.ctr.contains(av._1)) {
      if (Counter.ctr(av._1) > 1) {
        // do weak update
        var combinedValue: AbstractValue = av._2
        if (sto.contains(av._1)) {
          combinedValue = sto(av._1) ⊔ combinedValue
        }

        var tuple: (Address, AbstractValue) = (av._1, combinedValue)
        Store(sto + tuple)
      } else {
        // do strong update
        Store(sto + av)
      }
    } else {
      // do strong update
      Store(sto + av)
    }
  }

  // ditto for sequences of (address,value)
  def ++(avs: List[(Address, AbstractValue)]): Store = {
    var returnstr: Store = this
    avs.foreach { av =>
      returnstr = returnstr + av
    }
    returnstr
  }

  // add a value to the store at the given address during decl
  def up(av: (Address, AbstractValue)): Store = {
    if (Counter.ctr.contains(av._1)) {
      if (Counter.ctr(av._1) > 1) {
        // do weak update
        var combinedValue: AbstractValue = av._2
        // Sometimes it goes to the if part. Need to check what exactly causes this.
        if (sto.contains(av._1)) {
          combinedValue = sto(av._1) ⊔ combinedValue
        }

        var tuple: (Address, AbstractValue) = (av._1, combinedValue)
        Store(sto + tuple)
      } else {
        // do strong update
        var temp = Counter.ctr(av._1) + 1
        Counter.ctr += (av._1 -> temp)
        Store(sto + av)
      }
    } else {
      // do strong update
      Counter.ctr += (av._1 -> 1)
      Store(sto + av)
    }
  }

  // ditto for sequences of (address,value) during decl
  def upp(avs: List[(Address, AbstractValue)]): Store = {
    var returnstr: Store = this
    avs.foreach { av =>
      returnstr = returnstr up av
    }
    returnstr
  }

  def gc(rootset: LinkedHashSet[Address]): Store = {
    var unreachableAddresses: Set[Address] = (sto.keySet -- rootset)
    // Remove the unreachable address from the counter map
    for (address <- unreachableAddresses) {
      Counter.ctr += (address -> 0)
    }
    // Remove all the elements from the Store that are not in the root set.
    Store(sto)
  }

}

// abstract addresses (Trace, which is a seq of integer)
case class Address(lbl: Trace)

// companion object for factory method
object Address {

  // helpers for generating fresh addresses
  private var aid = 0
  private def fresh(): Int =
    { aid += 1; aid }

  // generate fresh Address
  def apply(): Address = {
    var stack: Stack[Int] = new Stack() :+ fresh()
    new Address(kcfa(stack))
  }

  def apply(num: Int): Address = {
    var stack: Stack[Int] = new Stack() :+ num
    new Address(kcfa(stack))
  }

}

sealed abstract class AbstractValue {
  // lattice join
  def ⊔(v: AbstractValue): AbstractValue

  // widening operator
  def ▽(v: AbstractValue): AbstractValue

  // binary ops
  def +(v: AbstractValue): AbstractValue
  def −(v: AbstractValue): AbstractValue
  def ×(v: AbstractValue): AbstractValue
  def ÷(v: AbstractValue): AbstractValue
  def ≈(v: AbstractValue): AbstractValue
  def ≠(v: AbstractValue): AbstractValue
  def <(v: AbstractValue): AbstractValue
  def ≤(v: AbstractValue): AbstractValue
  def ∧(v: AbstractValue): AbstractValue
  def ∨(v: AbstractValue): AbstractValue

  // for evaluating conditional guards: definitelyTrue returns true
  // iff this value represents at least one integer and definitely
  // could not be 0; definitelyFalse returns true iff this value
  // definitely represents 0 and nothing else; notEmpty returns true
  // iff this value represents at least one integer.
  //
  def definitelyTrue: Boolean
  def definitelyFalse: Boolean
  def notEmpty: Boolean
}

case class KontSet(set: LinkedHashSet[Kont] = LinkedHashSet()) extends AbstractValue {
  def ⊔(v: AbstractValue) = {
    v match {
      case KontSet(set1) => {
        KontSet(set ++ set1)
      }
      case _ => sys.error("undefined")
    }
  }

  // widening operator
  def ▽(v: AbstractValue) = this ⊔ v

  // binary ops
  def +(v: AbstractValue) = sys.error("undefined")
  def −(v: AbstractValue) = sys.error("undefined")
  def ×(v: AbstractValue) = sys.error("undefined")
  def ÷(v: AbstractValue) = sys.error("undefined")
  def ≈(v: AbstractValue) = sys.error("undefined")
  def ≠(v: AbstractValue) = sys.error("undefined")
  def <(v: AbstractValue) = sys.error("undefined")
  def ≤(v: AbstractValue) = sys.error("undefined")
  def ∧(v: AbstractValue) = sys.error("undefined")
  def ∨(v: AbstractValue) = sys.error("undefined")

  // for evaluating conditional guards: definitelyTrue returns true
  // iff this value represents at least one integer and definitely
  // could not be 0; definitelyFalse returns true iff this value
  // definitely represents 0 and nothing else; notEmpty returns true
  // iff this value represents at least one integer.
  //
  def definitelyTrue = sys.error("undefined")
  def definitelyFalse = sys.error("undefined")
  def notEmpty = sys.error("undefined")
}

// values: ℤ#
case class Value(intAbs: Z, closureSet: LinkedHashSet[Closure] = LinkedHashSet()) extends AbstractValue {

  // lattice join
  def ⊔(v: AbstractValue): AbstractValue = {
    v match {
      case Value(intAbs1, closureSet1) => {
        Value(Z(intAbs ⊔ intAbs1), closureSet ++ closureSet1)
      }
      case _ => sys.error("undefined")
    }
  }

  // widening operator
  def ▽(v: AbstractValue): AbstractValue = {
    v match {
      case Value(intAbs1, closureSet1) => {
        Value(Z(intAbs ▽ intAbs1), closureSet ++ closureSet1)
      }
      case _ => sys.error("undefined")
    }
  }

  // binary ops
  def +(v: AbstractValue): AbstractValue = {
    v match {
      case Value(intAbs1, closureSet1) => {
        Value(Z(intAbs + intAbs1))
      }
      case _ => sys.error("undefined")
    }
  }

  def −(v: AbstractValue): AbstractValue = {
    v match {
      case Value(intAbs1, closureSet1) => {
        Value(Z(intAbs − intAbs1))
      }
      case _ => sys.error("undefined")
    }
  }

  def ×(v: AbstractValue): AbstractValue = {
    v match {
      case Value(intAbs1, closureSet1) => {
        Value(Z(intAbs × intAbs1))
      }
      case _ => sys.error("undefined")
    }
  }

  def ÷(v: AbstractValue): AbstractValue = {
    v match {
      case Value(intAbs1, closureSet1) => {
        Value(intAbs ÷ intAbs1)
      }
      case _ => sys.error("undefined")
    }
  }

  def ≈(v: AbstractValue): AbstractValue = {
    v match {
      case Value(intAbs1, closureSet1) => {
        Value(Z(intAbs ≈ intAbs1))
      }
      case _ => sys.error("undefined")
    }
  }

  def ≠(v: AbstractValue): AbstractValue = {
    v match {
      case Value(intAbs1, closureSet1) => {
        Value(Z(intAbs ≠ intAbs1))
      }
      case _ => sys.error("undefined")
    }
  }

  def <(v: AbstractValue): AbstractValue = {
    v match {
      case Value(intAbs1, closureSet1) => {
        Value(intAbs < intAbs1)
      }
      case _ => sys.error("undefined")
    }
  }

  def ≤(v: AbstractValue): AbstractValue = {
    v match {
      case Value(intAbs1, closureSet1) => {
        Value(Z(intAbs ≤ intAbs1))
      }
      case _ => sys.error("undefined")
    }
  }

  def ∧(v: AbstractValue): AbstractValue = {
    v match {
      case Value(intAbs1, closureSet1) => {
        Value(intAbs ∧ intAbs1)
      }
      case _ => sys.error("undefined")
    }
  }

  def ∨(v: AbstractValue): AbstractValue = {
    v match {
      case Value(intAbs1, closureSet1) => {
        Value(intAbs ∨ intAbs1)
      }
      case _ => sys.error("undefined")
    }
  }

  // for evaluating conditional guards: definitelyTrue returns true
  // iff this value represents at least one integer and definitely
  // could not be 0; definitelyFalse returns true iff this value
  // definitely represents 0 and nothing else; notEmpty returns true
  // iff this value represents at least one integer.
  //
  def definitelyTrue: Boolean = {
    intAbs.definitelyTrue
  }

  def definitelyFalse: Boolean = {
    intAbs.definitelyFalse
  }

  def notEmpty: Boolean = {
    intAbs.notEmpty || closureSet.size > 0
  }

  override def toString = {
    "{" + intAbs + ", " + closureSet + "}"
  }

}

// integer abstraction: the constants lattice
//
//           ⊤
//         / | \
// ... -2 -1 0 1 2 ...
//         \ | /
//           ⊥
//
// we'll represent ⊥ as an empty set, a constant as a singleton set,
// and ⊤ as a doubleton set that does not contain a zero (look at the
// implicit conversion to see how this is enforced)
//
case class Z(ns: Set[BigInt]) {
  // import stuff from companion object
  import Z._

  def ⊔(v: Z) =
    v match {
      case Z(ns2) ⇒ ns ++ ns2
      case _ ⇒ sys.error("undefined")
    }

  def ▽(v: Z) =
    this ⊔ v

  def +(v: Z) =
    v match {
      case Z(ns2) ⇒ for (a ← ns ns; b ← ns2) yield a + b
      case _ ⇒ sys.error("undefined")
    }

  def −(v: Z) =
    v match {
      case Z(ns2) ⇒ for (a ← ns ns; b ← ns2) yield a - b
      case _ ⇒ sys.error("undefined")
    }

  def ×(v: Z) =
    v match {
      case Z(ns2) ⇒ for (a ← ns ns; b ← ns2) yield a * b
      case _ ⇒ sys.error("undefined")
    }

  // we can't use for..yield because it would make e.g. {1} ÷ {3,5} = {0},
  // but it needs to equal ⊤
  def ÷(v: Z) =
    v match {
      case n: Z if !(this.notEmpty && n.notEmpty) || n.definitelyFalse ⇒ ⊥
      case Z(ns2) if ns.size == 1 && ns2.size == 1 ⇒ Z(Set(ns.head / ns2.head))
      case n: Z ⇒ ⊤
      case _ ⇒ sys.error("undefined")
    }

  def ≈(v: Z) =
    v match {
      case Z(ns2) ⇒ for (a ← ns ns; b ← ns2) yield if (a == b) BigInt(1) else BigInt(0)
      case _ ⇒ sys.error("undefined")
    }

  def ≠(v: Z) =
    Z(Set(1)) − (this ≈ v)

  // same note as for ÷
  def <(v: Z) =
    v match {
      case n: Z if !(this.notEmpty && n.notEmpty) ⇒ ⊥
      case Z(ns2) if ns.size == 1 && ns2.size == 1 ⇒
        if (ns.head < ns2.head) True else False
      case n: Z ⇒ ⊤
      case _ ⇒ sys.error("undefined")
    }

  def ≤(v: Z) =
    (this ≈ v) + (this < v)

  // same note as for ÷
  def ∧(v: Z) =
    v match {
      case n: Z if !(this.notEmpty && n.notEmpty) ⇒ ⊥
      case n: Z if this.definitelyFalse || v.definitelyFalse ⇒ False
      case n: Z if this.definitelyTrue && v.definitelyTrue ⇒ True
      case n: Z ⇒ ⊤
      case _ ⇒ sys.error("undefined")
    }

  // same note as for ÷
  def ∨(v: Z) =
    v match {
      case n: Z if !(this.notEmpty && n.notEmpty) ⇒ ⊥
      case n: Z if this.definitelyFalse && v.definitelyFalse ⇒ False
      case n: Z if this.definitelyTrue || v.definitelyTrue ⇒ True
      case n: Z ⇒ ⊤
      case _ ⇒ sys.error("undefined")
    }

  def definitelyTrue =
    ns.size == 1 && ns.head != 0

  def definitelyFalse =
    ns.size == 1 && ns.head == 0

  def notEmpty =
    ns.nonEmpty

  // implicit conversion: this method is used to make sure a ⊤ value
  // (i.e., doubleton set) doesn't contain any zeros; this makes some
  // of the operations easier.
  implicit def ns2Z(ns: Set[BigInt]): Z =
    if (ns.size > 1) ⊤ else Z(ns)

  override def toString =
    if (ns.size == 0) "BOTTOM"
    else if (ns.size == 1) ns.head.toString
    else "TOP"
}

// companion object
object Z {
  // abstraction function
  def α(n: BigInt): Z =
    Z(Set(n))

  // a convenient shorthand for the ⊤, ⊥, true, and false values
  val ⊤ = Z(Set(3, 5))
  val ⊥ = Z(Set())
  val True = Z(Set(1))
  val False = Z(Set(0))
}
// closure
case class Closure(ρ: Env, f: Fun) {
  override def toString = "— Closure " + ρ + ", " + f
}

// semantic continuations
sealed abstract class Kont

case object haltK extends Kont {
  override def toString = "— haltK"
}

case class addrK(a: Address) extends Kont {
  override def toString = "— addrK " + a
}

case class seqK(ss: List[Stmt], κ: Kont) extends Kont {
  override def toString = (if (!ss.isEmpty) "— " + pretty(Seq(ss)) +
    "\n"
  else "— seq □\n") + κ
}

case class whileK(e: Exp, s: Stmt, κ: Kont) extends Kont {
  override def toString = "— while (" + pretty(e) + ") { " + pretty(s) +
    " }\n" + κ
}

case class retK(ρ: Env, x: Var, κ: Kont) extends Kont {
  override def toString = "— return (" + pretty(x) + " := )\n" + κ
}

sealed abstract class Trace {
  def +(n: Int): Trace  // push call site to stack
  def -(): Trace // pop call site from stack

}

// kcfa stack based control flow analysis.
case class kcfa(stk: Stack[Int] = new Stack()) extends Trace {

  // k-limited : k is taken from the global object Counter.k
  def apply(lbl: Int): kcfa = {
    if(stk.size < Counter.k) {
      kcfa(stk :+ lbl)
    }
    this
  }
  def +(lbl: Int): kcfa = {
    if(stk.size < Counter.k) {
      kcfa(stk :+ lbl)
    }
    this
  }

  def -(): kcfa = {
    if (!stk.isEmpty) {
      stk.pop
    }
    this
  }

}
package cs320

package object ex02 extends Exercise02 {
  // Problem 1
  def freeIds(expr: Expr): Set[String] = {
    
    def Idt(e: Expr):Set[String] = e match{
    case Num(num) => Set()
    case Add(left, right) => Idt(left) | Idt(right) 
    case Sub(left, right) => Idt(left) | Idt(right) 
    case Val(name, expr, body) => Idt(expr) | Idt(body) - name
    case Id(id) => Set(id)
    }
    Idt(expr)
  }

  // Problem 2
  def bindingIds(expr: Expr): Set[String] = {
    
    def Idt(e: Expr):Set[String] = e match{
    case Num(num) => Set()
    case Add(left, right) => Idt(left) | Idt(right) 
    case Sub(left, right) => Idt(left) | Idt(right) 
    case Val(name, expr, body) => Set(name) | Idt(expr) | Idt(body)
    case Id(id) => Set()
    }
    Idt(expr)
  }

  // Problem 3
  def boundIds(expr: Expr): Set[String] = {
    
    def Idt(e: Expr):Set[String] = e match{
    case Num(num) => Set()
    case Add(left, right) => Idt(left) | Idt(right) 
    case Sub(left, right) => Idt(left) | Idt(right) 
    case Val(name, expr, body) => Idt(expr) | Idt(body) -- freeIds(e)
    case Id(id) => Set(id)
    }
    Idt(expr)
  }
  
  /* sample sol
  def boundIds(expr: Expr): Set[String] = {
      def bounds(e: Expr, ids: Set[String]): Set[String] = e match {
      case Num(n) => Set()
      case Add(left, right) => bounds(left, ids) ++ bounds(right, ids)
      case Sub(left, right) => bounds(left, ids) ++ bounds(right, ids)
      case Val(name, expr, body) => bounds(expr, ids) ++ bounds(body, ids + name)
      case Id(id) => if (ids contains id) Set(id) else Set()
    }
    bounds(expr, Set())
  }*/ 

  // Tests
  def tests: Unit = {
    test(freeIds(Expr("{ val x = 1; (x + y) }")), Set("y"))
    test(freeIds(Expr("{ val z = 2; 1 }")), Set())
    test(bindingIds(Expr("{ val x = 1; (x + y) }")), Set("x"))
    test(bindingIds(Expr("{ val z = 2; 1 }")), Set("z"))
    test(boundIds(Expr("{ val x = 1; (x + y) }")), Set("x"))
    test(boundIds(Expr("{ val z = 2; 1 }")), Set())

    /* Write your own tests */
  }

  def test2: Unit = {
    // tests for freeIds
    test(freeIds(Expr("{ val x = 3; (x + (3 - x)) }")), Set())
    test(freeIds(Expr("{ val x = 3; (a - (4 + x)) }")), Set("a"))
    test(freeIds(Expr("{ val x = 3; (b - (a - x)) }")), Set("a", "b"))
    test(freeIds(Expr("{ val x = 3; (a - (b - (x + b))) }")), Set("a", "b"))
    test(freeIds(Expr("{ val x = 3; (y - { val y = 7; (x + (b - a)) }) }")), Set("a", "b", "y"))
    test(freeIds(Expr("{ val x = t; (x - { val y = y; (x + (b - a)) }) }")), Set("a", "b", "t", "y"))
    test(freeIds(Expr("{ val x = { val y = 3; (x - y) }; (x + y) }")), Set("x", "y"))
    test(freeIds(Expr("({ val x = 10; { val x = 3; (y - { val y = 7; (x + (c - b)) }) } } + { val a = a; a })")), Set("a", "b", "c", "y"))
    test(freeIds(Expr("({ val x = 10; { val x = 3; (y - { val y = 7; (x + (c - b)) }) } } + { val a = d; a })")), Set("b", "c", "d", "y"))
    test(freeIds(Expr("({ val x = 10; { val x = 3; (y - { val y = 7; (x + (c - b)) }) } } + { val a = d; z })")), Set("b", "c", "d", "y", "z"))

    // tests for bindingIds
    test(bindingIds(Expr("(3 + (x - y))")), Set())
    test(bindingIds(Expr("{ val y = 3; { val x = x; y } }")), Set("x", "y"))
    test(bindingIds(Expr("{ val y = 3; { val y = x; (x + y) } }")), Set("y"))
    test(bindingIds(Expr("{ val y = 3; { val y = { val x = (3 + y); (x - y) }; (x + y) } }")), Set("x", "y"))
    test(bindingIds(Expr("{ val z = 3; { val w = { val z = (3 + y); (x - y) }; { val w = y; (7 + w) } } }")), Set("w", "z"))

    // tests for boundIds
    test(boundIds(Expr("{ val x = 3; (y + 3) }")), Set())
    test(boundIds(Expr("{ val x = 3; (x + (x - y)) }")), Set("x"))
    test(boundIds(Expr("{ val x = 3; (x + { val y = 7; (x - y) }) }")), Set("x", "y"))
    test(boundIds(Expr("{ val x = 3; { val y = x; (3 - y) } }")), Set("x", "y"))
    test(boundIds(Expr("{ val x = 3; (y + { val y = x; (3 - 7) }) }")), Set("x"))
    test(boundIds(Expr("{ val x = x; (y + { val y = y; (3 - { val z = 7; (z - x) }) }) }")), Set("x", "z"))
    test(boundIds(Expr("{ val x = { val y = 3; (x + y) }; (y + { val y = y; (3 - 7) }) }")), Set("y"))
    test(boundIds(Expr("{ val x = a; { val y = b; { val z = c; (d + (x - (y + z))) } } }")), Set("x", "y", "z"))
    test(boundIds(Expr("({ val x = 10; { val x = 3; (y - { val y = 7; (x + (c - b)) }) } } + { val a = d; a })")), Set("a", "x"))
    test(boundIds(Expr("({ val x = 10; { val x = 3; (y - { val y = 7; (x + (c - b)) }) } } + { val a = d; z })")), Set("x"))
  }
}

interface Adder {
  def add(x : float, y : float) : float;
}

component CAdder provides Adder {
  def add(x : float, y : float) : float {
    return x + y;
  }
}

component EntryPoint provides App uses Adder {
  def main() : int {
    print( add(17.5, 25.5) );
    return 0;
  }
}

connect EntryPoint.Adder <- CAdder.Adder;

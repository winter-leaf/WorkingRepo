---
title: Design Patter - Factory Pattern
top: false
cover: false
toc: true
mathjax: true
date: 2020-05-25 20:19:28
password:
summary:
tags: Design Pattern
categories: pattern
---

Factory pattern的实质上就是一个实例对象产生器。这里的实力对象一般是指进行了多态的对象。
<!--- more -->
Factory pattern还有一个延展的形式，叫做abstract factory pattern，其本质就是factory的factory，factory本身也进行多态构造。

# 1. Factory pattern + abstract factory pattern
话不多说，看一个例子就明白了
~~~verilog
// virtual base transformer
virtual class Transformer;
  string name;
  string force_;
  int height;
  int power;
  
  function new(string name, force_, int height, power);
    this.name = name;
	this.force_ = force_;
	this.height = height;
	this.power = power;
    $display("---> name = %0s, force = %0s, height = %0d, power = %0d", this.name, this.force_, this.height, this.power);
  endfunction
endclass

class Megatron extends Transformer;
  function new(string name, force_, int height, power);
    super.new(name, force_, height, power);
  endfunction
endclass


class OptimusPrime extends Transformer;
  function new(string name, force_, int height, power);
    super.new(name, force_, height, power);
  endfunction
endclass

class Bumblebee extends Transformer;
  function new(string name, force_, int height, power);
    super.new(name, force_, height, power);
  endfunction
endclass


class Starscream extends Transformer;
  function new(string name, force_, int height, power);
    super.new(name, force_, height, power);
  endfunction
endclass


// virtual base factory
virtual class TransformerFactory;
  function new();
  endfunction

  virtual function Transformer makeTransformer(string name);
    $display("****** Forging %0s... done! ******:", name);
  endfunction 
endclass


//  Decepticon Factory
class DecepticonFactory extends TransformerFactory;
  function new();
  endfunction

  function Transformer makeTransformer(string name);
	super.makeTransformer(name);
    case(name)
      "Megatron": begin
        Megatron meg = new("Megatron", "Decepticon", 80, 100);
        return meg;
      end
      
      "Starscream": begin
        Starscream star = new("Starscream", "Decepticon", 93, 90);
        return star;
      end
    endcase
  endfunction
endclass


// Autobot Factory
class AutobotFactory extends TransformerFactory;
  function new();
  endfunction

  function Transformer makeTransformer(string name);
	super.makeTransformer(name);
    case(name)
	  "OptimusPrime": begin
        OptimusPrime opt = new("OptimusPrime", "Autobot", 100, 100);
        return opt;
      end
      
      "Bumblebee": begin
        Bumblebee bum = new("Bumblebee", "Autobot", 85, 90);
        return bum;
      end
    endcase
  endfunction
endclass

// factory of factory
class Cybertron;
  function new();
  endfunction
  
  function TransformerFactory chooseForce(string force_); 
    case(force_)
	  "Decepticon": begin
	    DecepticonFactory df = new();
		return df;
      end
	  "Autobot": begin
	    AutobotFactory af = new();
		return af;
      end
	endcase
  endfunction
endclass


module top();
  initial begin
    Cybertron cybertron = new();
    
    TransformerFactory autobot_factory = cybertron.chooseForce("Autobot");
    Transformer opt = autobot_factory.makeTransformer("OptimusPrime");
    Transformer bum = autobot_factory.makeTransformer("Bumblebee");
    
    TransformerFactory megatron_factory = cybertron.chooseForce("Decepticon");
    Transformer meg = megatron_factory.makeTransformer("Megatron");
    Transformer star = megatron_factory.makeTransformer("Starscream");
  end
endmodule
~~~

例子中，AutobotFactory和DecepticonFactory就是简单的factory pattern，又称为factory method pattern。
Cybertron是factory的factory，结合AutobotFactory，DecepticonFactory与TransformerFactory的多态结构，就是abstract factory pattern。


# 2. when to use this pattern?
当有多个多态实例要动态生成时，可以使用。

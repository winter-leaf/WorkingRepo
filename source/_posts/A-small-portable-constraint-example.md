---
title: A small portable constraint example
top: false
cover: false
toc: true
mathjax: true
date: 2020-08-17 20:51:43
password:
summary:
tags: randomization
categories: SystemVerilog
---


记录一下个人感觉比较有趣的动态添加删除约束的方法。

<!--- more --->

此方法的本质是利用randomize会随机化所有可见rand变量的机制，通过提供外部约束对象handle来将此对象的约束施加到带约束rand变量上。
具体看一个例子就知道了。

# 方法介绍
~~~
// -------------------------------------------
// 约束基类. 用于连接约束与待约束对象
// -------------------------------------------
class constraint_rule_base#(type T);
   T item_to_constrain;
   string name;

   function new(string name);
      this.name = name;
   endfunction : new

   virtual function void grab_item(T item_to_constrain);
      this.item_to_constrain = item_to_constrain;
   endfunction : grab_item

   virtual function void release_item();
      this.item_to_constrain = null;
   endfunction : release_item
   
endclass : constraint_rule_base

// -------------------------------------------------------------------------------------------
// 约束集合基类. 用于整合各个约束实例，并连接各个实例与待约束对象
// -------------------------------------------------------------------------------------------
class constraint_rule_collection#(type T) extends constraint_rule_base#(T);
   typedef constraint_rule_base#(T) constr_rule_t;
   rand constr_rule_t rules[string];

   function new(string name, T item_to_constrain);
      super.new(name);
      this.grab_item(item_to_constrain);
   endfunction : new
  
   function void add_rule(constr_rule_t rule);
      if(this.item_to_constrain == null) begin
	 $fatal("item to be constrained must be given before add new rules");
      end
      this.rules[rule.name] = rule;
      this.rules[rule.name].grab_item(this.item_to_constrain);
   endfunction : add_rule

   function void delete_rule(string name);
      if(rules.exists(name)) begin
	 this.rules[name].release_item();
	 this.rules.delete(name);
      end
   endfunction : delete_rule

endclass : constraint_rule_collection


module tb();

  typedef class A;
  
   class rule_legal_range extends constraint_rule_base#(A);
      function new(string name);
	 super.new(name);
      endfunction : new
     
      constraint c_legal_range {
         this.item_to_constrain.value inside {[0:10]};
      }
   endclass : rule_legal_range
    
    
   class rule_illegal_range extends constraint_rule_base#(A); 
      function new(string name);
	 super.new(name);
      endfunction : new
     
      constraint c_illegal_range {
         !(this.item_to_constrain.value inside {[4:8]});
      }
   endclass : rule_illegal_range
  

   class A;
      rand int value;
      function void post_randomize();
	$display("randomized value = %0d", this.value);
      endfunction : post_randomize
   endclass : A


   class wrapper;
      rand A item;
      rand constraint_rule_collection#(A) constraints;
      rule_legal_range legal_range;
      rule_illegal_range illegal_range;

      function new();
     	 this.item = new();
     	 this.constraints = new("rules", this.item);
     	 this.legal_range = new("legal_range");
     	 this.illegal_range = new("illegal_range");
      endfunction : new


      function void run();
         $display("******** No rules applied *********");
         repeat(10) this.randomize();
		 
     	 $display("******** legal_range rule applied *********");
     	 this.constraints.add_rule(this.legal_range);
     	 repeat(10) this.randomize();
		 
     	 $display("******** illegal_range rule applied *********");
     	 this.constraints.add_rule(this.illegal_range);
     	 repeat(10) this.randomize();
		 
     	 $display("******** illegal_range rule deleted *********");
     	 this.constraints.delete_rule("illegal_range");
     	 repeat(10) this.randomize();
      endfunction : run

   endclass : wrapper

   initial begin
     wrapper w = new();
     w.run();
   end

endmodule : tb
~~~

输出结果如下:
> \*\*\*\*\*\*\*\* No rules applied \*\*\*\*\*\*\*\*
> randomized value = 409176739
> randomized value = -1430829098
> randomized value = 1575644161
> randomized value = 460882633
> randomized value = 114263597
> randomized value = -334823001
> randomized value = 1737418480
> randomized value = -439344846
> randomized value = -33398467
> randomized value = 21230490
> \*\*\*\*\*\*\*\* legal\_range\ rule applied \*\*\*\*\*\*\*\*
> randomized value = 1
> randomized value = 4
> randomized value = 9
> randomized value = 9
> randomized value = 6
> randomized value = 10
> randomized value = 5
> randomized value = 2
> randomized value = 7
> randomized value = 5
> \*\*\*\*\*\*\*\* illegal\_range\ rule applied \*\*\*\*\*\*\*\*
> randomized value = 1
> randomized value = 0
> randomized value = 9
> randomized value = 1
> randomized value = 0
> randomized value = 9
> randomized value = 10
> randomized value = 3
> randomized value = 3
> randomized value = 10
> \*\*\*\*\*\*\*\* illegal\_range rule deleted \*\*\*\*\*\*\*\*
> randomized value = 1
> randomized value = 4
> randomized value = 7
> randomized value = 4
> randomized value = 7
> randomized value = 3
> randomized value = 0
> randomized value = 6
> randomized value = 1
> randomized value = 2


一般情况下，我们可能想在待约束对象里直接定义约束，从而把相关的约束直接封装到对象定义里。那么可以这么做:
~~~
   class A;
      rand int value;
      rand constraint_rule_collection#(A) constraints;

      function new();
          rule_legal_range legal_range = new("legal_range");
          rule_illegal_range illegal_range = new("illegal_range");
          this.constraints = new("rules", this);
          this.constraints.add_rule(legal_range);
          this.constraints.add_rule(illegal_range);
      endfunction : new
   endclass : A
~~~


# 小缺陷
这种方法可以方便地实现动态添加和删除约束，但也有一个不方便的地方。
这种方法假设所有定义在约束对象内的约束都是相互独立的。但实际项目中，很有可能有很多的随机变量相互关联。
那么这种方法并不能很明显地体现出优势，反而会增加分割约束的工作量。一定程度上相当于人为地替solver做了partition工作。

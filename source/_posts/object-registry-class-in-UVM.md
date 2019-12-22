---
title: object registry class in UVM
top: false
cover: false
toc: true
mathjax: true
date: 2019-12-22 09:43:47
password:
summary:
tags: UVM
categories: SystemVerilog
---


上一篇提到了宏定义uvm_object_utils_begin(T)，里面有一个关键的类uvm_object_registry#(T,"S")，后面简称uor, 它是type_id与uvm_fatory注册的本质。这里再稍微展开看一下这个类。
<!---more--->

# 1. 宏观定义
~~~
uvm_object_registry#(type T=uvm_object, string Tname="<unknown>") 
    extends uvm_object_wrapper;

  typedef uvm_object_registry #(T,Tname) this_type;
  typedef uvm_registry_common#(this_type, uvm_registry_object_creator, T, Tname) common_type;
  
  virtual function uvm_object create_object(string name="");
  static function string type_name();
  virtual function string get_type_name();
  static function this_type get();
  static function T create(string name="", uvm_component parent=null, string contxt="");
  static function void set_type_override(uvm_object_wrapper override_type, bit replace=1);
  static function void set_inst_override(uvm_object_wrapper override_type, string inst_path, uvm_component parent=null)；
  static function bit set_type_alias(string alias_name);
  virtual function void initialize();
endclass
~~~
uor是一个参数化并继承于uvm_object_wrapper的子类。uvm_object_wrapper可以暂时简单地看成是uvm_object的一个默认实现类，用于覆写uvm_object的实现。
这里比较关键的是common_type这个定义，它用到了和type_id定义时一样的方式来定义其他类型，并在后续的函数中会返回这个类的实例对象，本质上它的类型是uvm_registry_common#(this_type, uvm_registry_object_creator, T, Tname)，后面简称urc。这种形式会在后续经常看到。
common中用到的uvm_registry_object_creator是一个用于在factory中创建实例的类。它有一个create_by_type()函数，这个函数会在factory中，根据类名和层级路径名来创建一个实例。

# 2. 内部定义的函数
- create_object(string name="")
这个函数在源码中解释到，它是一个对父类函数的一个覆写，会被factory在确定好实例的创建类型时调用。此函数不应该被直接调用，而应该用后边的create()函数。

- string type_name()
这个函数仅是返回urc的类型名。这个类型名默认时是传入的Tname，如果Tname没有给定则会搜索一个别名。可以简单地理解为返回一个代表类型名的字符串。

- string get_type_name()
本质上和type_name()是一样的，返回代表类型的字符串，只不过相比于type_name()，get_type_name()会先实例化一个urc类的对象，并返回这个对象的类型名字符串。

- this_type get()
这个函数会返回uor类的实例对象。

- T create(string name="", uvm_component parent=null, string contxt="")
这个函数是一个关键的函数，它本质上是调用了urc的create()函数，而urc的create()函数会进行底层的实例创建。
这里的三个形参，第一个是在factory中的对象名，一般用于factory override。第二个是上层uvm组件，就是在创建uvm_component时的parent参数，代表是哪个上层对象创建了它。第三个contxt是层级的路径名。
这三个形参会原封不动地送入urc地create()函数。在urc中，它会根据是否提供了parent和contxt值来决定是否进行自动赋值。如果给定了parent和contxt，就使用给定值，否则会利用parent.get_full_name()来获取层级路径名。接着会使用uvm_registry_object_creator在factory中创建并返回一个T类的实例对象。T是一开始，继承于uvm_object，用户自定义的类。

- set_type_override和set_inst_override
这两个函数就是常用的factory override函数。用于替换实例对象。

- set_type_alias(string alias_name)
这个函数用于给类名取一个别名。在urc里面有一个队列m__type_aliases[$]用于存储这些别名。

- initialize()
这个函数的主要作用是根据类型名在factory中把创建的对象登记进factory。


# 3. 小结
uvm_object_registry#(T,"S")是一个介于用户自定义的类和uvm_factory之间的一个类，更像是起到一个代理类的作用。它负责在uvm_factory中"登记/注册"和"创建"用户自定义的类的实例。

---
title: UVM heartbeat - a wachdog mechnism and a small framework
top: false
cover: false
toc: true
mathjax: true
date: 2020-06-02 20:42:26
password:
summary:
tags: UVM
categories: SystemVerilog
---

UVM heartbeat是一个类似看门狗的机制。

<!---more--->

工作过程大致如下:
1. 建立一个监听器
2. 建立一个共享的“回声”令牌
3. 将令牌分给待监测元件
4. 监听器对令牌进行定时段式的“回声”检测
5. 被分到令牌的元件通过令牌制造“回声”
6. 如果监听器在拟定时段内听到“回声”则工作正常，否则报错

这里的回声在代码中是uvm_callbacks_objection类型的一个实例。这个实例会分到各个待监测的元件中。在元件进行运作时不停的对其raise_objection()来制造“回声”。
在监听器侧，监测器通过一个uvm_event来触发监测动作。

uvm_heartbeat机制并不是必要的。所以多数UVM测试平台都不会加入此机制。这就造成里一个在后期对已有测试平台植入的困难。
经过实验，阅读和一些思考，暂时想到了一个较为轻松的heartbeat植入框架，目的是在少量改动原测试平台的基础上加入heartbeat机制。
下面看一个框架的例子

~~~verilog
import uvm_pkg::*;
`include "uvm_macros.svh"

class heartbeat_fatal_catcher extends uvm_report_catcher;

  local uvm_callbacks_objection beat_echo;

  `uvm_object_utils(heartbeat_fatal_catcher)

  function new(string name="heartbeat_fatal_catcher");
    super.new(name);
  endfunction

  function action_e catch();
    if(get_severity() == UVM_FATAL && get_id() == "HBFAIL") begin
      `uvm_error("HBFAIL", $psprintf("Heartbeat failure! Objections:"));
      this.beat_echo.display_objections();
    end
    return THROW;
  endfunction

  function void set_beat_echo(uvm_callbacks_objection beat_echo);
    this.beat_echo = beat_echo;
  endfunction : set_beat_echo
endclass : heartbeat_fatal_catcher


class heartbeat_cfg extends uvm_heartbeat;
  local int m_check_period;

  // uvm_heartbeat doesn't register to factory in base,
  // cannot use `uvm_object_utils(heartbeat_cfg)

  function new(string name,
               int check_period,
               uvm_component cntxt,
               uvm_callbacks_objection beat_echo = null);
    super.new(name, cntxt, beat_echo);
    if(beat_echo == null) begin
      `uvm_fatal("HBCFG", "beat echo(the heartbeat objection) must be provided")
    end
    this.set_check_period(check_period);
  endfunction : new

  function int get_check_period();
    return this.m_check_period;
  endfunction : get_check_period

  function int set_check_period(int check_period);
    if(check_period < 0) begin
      `uvm_fatal("HBCFG", "check period must be >= 0")
    end
    this.m_check_period = check_period;
  endfunction : set_check_period

endclass : heartbeat_cfg


class heartbeat_monitor extends uvm_component;
  local heartbeat_cfg cfg;
  local uvm_event do_listen;
  local uvm_callbacks_objection beat_echo;

  `uvm_component_utils_begin(heartbeat_monitor)
  `uvm_component_utils_end

  function new(string name="heartbeat_monitor", uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    this.do_listen = new("do_listen");
    this.beat_echo = new("beat_echo");
  endfunction : build_phase

  function void start_of_simulation_phase(uvm_phase phase);
    super.start_of_simulation_phase(phase);
    this.start(phase);
  endfunction

  function void init(uvm_component cntxt,
                     string inst_name_pattern,
                     uvm_heartbeat_modes mode,
                     int check_period);
    uvm_component comps[$];
    string pattern_full_name;

    pattern_full_name = $sformatf("%0s.%0s", cntxt.get_full_name(), inst_name_pattern);
    uvm_root::get().find_all(pattern_full_name, comps, cntxt);
    if(comps.size() == 0) begin
      `uvm_warning("HBMON", "Didn't find any component with given name pattern, will use all components from given cntxt downward.")
    end

    this.cfg = new("heartbeat_cfg", check_period, cntxt, this.beat_echo);
    this.cfg.set_heartbeat(null, comps); // null: dont start immediately
    this.cfg.set_mode(mode);
    this.set_fatal_cather();
  endfunction : init

  function void set_fatal_cather();
    heartbeat_fatal_catcher hb_fatal_catcher;
    hb_fatal_catcher = heartbeat_fatal_catcher::type_id::create("hb_fatal_catcher");
    hb_fatal_catcher.set_beat_echo(this.beat_echo);
    // null: apply to all objects in hierarchy that caught the "HBFAIL" msg
    uvm_report_cb::add(null, hb_fatal_catcher);
  endfunction : set_fatal_cather

  task start(uvm_phase phase);
    if(this.cfg.get_check_period() != 0) begin
      this.cfg.start(this.do_listen);
      fork
        this.listen_echo();
        forever begin
          int check_period = this.cfg.get_check_period();
          // quit if external sets period to 0 while running
          if(check_period != 0) begin
            #check_period;
            this.listen_echo();
          end else begin
            break;
          end
        end
      join_none
      `uvm_info("HBMON", "heartbeat monitor started", UVM_HIGH)
    end
  endtask : start

  function void listen_echo();
    `uvm_info("HBMON",
              $sformatf("heartbeat monitor listens to beat echo"),
              UVM_MEDIUM)
    this.do_listen.trigger();
  endfunction : listen_echo

  function uvm_callbacks_objection get_beat_echo();
    return this.beat_echo;
  endfunction : get_beat_echo

endclass : heartbeat_monitor

class base_component extends uvm_component;
  protected uvm_callbacks_objection beat_echo;

  `uvm_component_utils(base_component)

  function new(string name="base_component", uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void set_beat_echo(uvm_callbacks_objection beat_echo);
    this.beat_echo = beat_echo;
  endfunction : set_beat_echo

  function void echo();
    `uvm_info(this.get_type_name(),
                $sformatf("%0s beats", this.get_full_name()),
                UVM_MEDIUM)
    this.beat_echo.raise_objection(this);
  endfunction : echo

endclass : base_component


class component_a extends base_component;
  `uvm_component_utils(component_a)

  function new(string name="component_a", uvm_component parent);
    super.new(name, parent);
  endfunction : new

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    for(int i=1;i<10;i++) begin
      #(30*i);
      this.echo();
    end
    phase.drop_objection(this);
  endtask : run_phase
endclass : component_a


class component_b extends base_component;
  `uvm_component_utils(component_b)

  function new(string name="component_b", uvm_component parent);
    super.new(name, parent);
  endfunction : new

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    for(int i=1;i<10;i++) begin
      #(55*i);
      this.echo();
    end
    phase.drop_objection(this);
  endtask : run_phase
endclass : component_b


class environment extends uvm_env;

  component_a comp_a;
  component_b comp_b;
  heartbeat_monitor hb_mon;

  `uvm_component_utils(environment)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    this.comp_a = component_a::type_id::create("comp_a", this);
    this.comp_b = component_b::type_id::create("comp_b", this);
    this.hb_mon = heartbeat_monitor::type_id::create("hb_mon", this);
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    this.hb_mon.init(this, "comp_*", UVM_ANY_ACTIVE, 100);
    this.comp_a.set_beat_echo(this.hb_mon.get_beat_echo());
    this.comp_b.set_beat_echo(this.hb_mon.get_beat_echo());
  endfunction : connect_phase

endclass : environment


class base_test extends uvm_test;
  environment env;

  `uvm_component_utils(base_test)

  function new(string name="base_test", uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    this.env = environment::type_id::create("env", this);
  endfunction : build_phase

endclass: base_test


module top();

  initial begin
    run_test("base_test");
  end

endmodule
~~~


框架例子中:
* heartbeat_monitor是回声监听器。
* heatbeat_cfg是heartbeat_monitor的配置
* heartbeat_monitor中的beat_echo是回声令牌
* heartbeat_fatal_catcher是在听不到回声时起到扩展作用的一个报错信息捕捉器。

运行过程如下:
1. 通过init()，在env中设定好待监听元件所在的位置区域，监听模式(UVM_ALL_ACTIVE, UVM_ONE_ACTIVE, UVM_ANY_ACTIVE, UVM_NO_HB_MODE四种模式, 分别对应:监听全部，监听任意一个，监听一个，不监听)，监听周期。
2. heartbeat_monitor会自动在start_of_simulation_phase启动，并在后台做周期性监听。
3. 在监听区域的元件通过echo()制造回城，来告知heartbeat_monitor自己的活动状态。

框架整体上只需设置heartbeat_monitor.init()函数，以及在对应的待监听元件中传递好回声令牌，并定时地调动echo()函数即可。元件层面，需要元件派生自base_component来获得相应的成员变量及echo()函数。 相对地容易植入已存在的测试平台。

这套框架的其他特点:
1. 待监听元件所在的位置区域设置采用与uvm_config_db一样的路径设置方法。
2. 由于heartbeat机制本身报错时并不会显示回声触发次数及触发源头的统计，可能会导致调试信息缺失。heartbeat_fatal_catcher的加入会补充显示这些统计。
3. 这个可能不算是框架的特点，更算是heartbeat机制本身的特点 –  即使元件没有划分到设定好的待监听区域，但只要在监听时段内此元件也通过回声令牌制造了回声，那么它也会被列入监听范围内。

下面是运行的结果:
> UVM_INFO @ 0: reporter [RNTST] Running test base_test...
> UVM_INFO tests.sv(130) @ 0: uvm_test_top.env.hb_mon [HBMON] heartbeat monitor listens to beat echo
> UVM_INFO tests.sv(156) @ 30: uvm_test_top.env.comp_a [component_a] uvm_test_top.env.comp_a beats
> UVM_INFO tests.sv(156) @ 55: uvm_test_top.env.comp_b [component_b] uvm_test_top.env.comp_b beats
> UVM_INFO tests.sv(156) @ 90: uvm_test_top.env.comp_a [component_a] uvm_test_top.env.comp_a beats
> UVM_INFO tests.sv(130) @ 100: uvm_test_top.env.hb_mon [HBMON] heartbeat monitor listens to beat echo
> UVM_INFO tests.sv(156) @ 165: uvm_test_top.env.comp_b [component_b] uvm_test_top.env.comp_b beats
> UVM_INFO tests.sv(156) @ 180: uvm_test_top.env.comp_a [component_a] uvm_test_top.env.comp_a beats
> UVM_INFO tests.sv(130) @ 200: uvm_test_top.env.hb_mon [HBMON] heartbeat monitor listens to beat echo
> UVM_INFO tests.sv(156) @ 300: uvm_test_top.env.comp_a [component_a] uvm_test_top.env.comp_a beats
> UVM_INFO tests.sv(130) @ 300: uvm_test_top.env.hb_mon [HBMON] heartbeat monitor listens to beat echo
> UVM_INFO tests.sv(156) @ 330: uvm_test_top.env.comp_b [component_b] uvm_test_top.env.comp_b beats
> UVM_INFO tests.sv(130) @ 400: uvm_test_top.env.hb_mon [HBMON] heartbeat monitor listens to beat echo
> UVM_INFO tests.sv(156) @ 450: uvm_test_top.env.comp_a [component_a] uvm_test_top.env.comp_a beats
> UVM_INFO tests.sv(130) @ 500: uvm_test_top.env.hb_mon [HBMON] heartbeat monitor listens to beat echo
> UVM_INFO tests.sv(156) @ 550: uvm_test_top.env.comp_b [component_b] uvm_test_top.env.comp_b beats
> UVM_INFO tests.sv(130) @ 600: uvm_test_top.env.hb_mon [HBMON] heartbeat monitor listens to beat echo
> UVM_INFO tests.sv(156) @ 630: uvm_test_top.env.comp_a [component_a] uvm_test_top.env.comp_a beats
> UVM_INFO tests.sv(130) @ 700: uvm_test_top.env.hb_mon [HBMON] heartbeat monitor listens to beat echo
> UVM_INFO tests.sv(130) @ 800: uvm_test_top.env.hb_mon [HBMON] heartbeat monitor listens to beat echo
> UVM_ERROR tests.sv(16) @ 800: uvm_test_top.env [HBFAIL] Heartbeat failure! Objections:
> UVM_INFO uvm-1.2/base/uvm_objection.svh(1076) @ 800: beat_echo [UVM/OBJ/DISPLAY] The total objection count is 10
> ---------------------------------------------------------
> Source  Total   
> Count   Count   Object
> ---------------------------------------------------------
> 0       10      uvm_top
> 0       10        uvm_test_top
> 0       10          env
> 6       6             comp_a
> 4       4             comp_b
> ---------------------------------------------------------
>  
> UVM_FATAL @ 800: uvm_test_top.env [HBFAIL] Did not recieve an update of beat_echo on any component since last event trigger at time 700. The list of registered components is:
>   uvm_test_top.env.comp_a
>   uvm_test_top.env.comp_b
> UVM_INFO uvm-1.2/base/uvm_report_catcher.svh(705) @ 800: reporter [UVM/REPORT/CATCHER] 
> --- UVM Report catcher Summary ---
>  
>  
> Number of demoted UVM_FATAL reports  :    0
> Number of demoted UVM_ERROR reports  :    0
> Number of demoted UVM_WARNING reports:    0
> Number of caught UVM_FATAL reports   :    0
> Number of caught UVM_ERROR reports   :    0
> Number of caught UVM_WARNING reports :    0

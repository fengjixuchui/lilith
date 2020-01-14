require "./prelude/primitives.cr"
require "./prelude/atomic.cr"
require "./core/object.cr"
require "./core/markable.cr"
require "./c/types.cr"
require "./c/*"
require "./core/*"
require "./sys/*"
require "./io/io.cr"
require "./io/*"
require "./time/*"
require "./gc/*"

lib LibCrystalMain
  fun __crystal_main(argc : Int32, argv : UInt8**)
end

fun __crystal_once_init : Void*
  Pointer(Void).new 0
end

fun __crystal_once(state : Void*, flag : Bool*, initializer : Void*)
  unless flag.value
    Proc(Nil).new(initializer, Pointer(Void).new 0).call
    flag.value = true
  end
end

fun main(argc : LibC::Int, argv : UInt8**) : LibC::Int
  stack_end = Pointer(Void).null # scan from here!
  {% if flag?(:i686) %}
    asm("mov %esp, $0" : "=r"(stack_end) :: "volatile")
    Allocator.init 0x8000_0000u64
    GC.init(Pointer(Void).new(0xFF80_0000u64), stack_end)
  {% else %}
    asm("mov %rsp, $0" : "=r"(stack_end) :: "volatile")
    Allocator.init 0x1_0000_0000u64, 0x40_0000_0000u64
    GC.init(Pointer(Void).new(0x7FFF_FF80_0000u64), stack_end)
  {% end %}
  LibCrystalMain.__crystal_main(argc, argv)
  STDOUT.flush
  0
end

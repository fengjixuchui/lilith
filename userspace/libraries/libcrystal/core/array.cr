require "./enumerable.cr"
require "./indexable.cr"

class Array(T) < Markable
  include Enumerable(T)
  include Indexable(T)

  @size = 0
  @capacity = 0
  getter size, capacity
  protected setter size

  @buffer = Pointer(T).null

  def to_unsafe
    @buffer
  end

  private def recalculate_capacity
    @capacity = Allocator.block_size_for_ptr(@buffer) // sizeof(T)
  end

  private def expand(new_capacity)
    if @size > new_capacity
      abort "size must be smaller than capacity"
    end
    if @buffer.null?
      @buffer = Pointer(T).malloc_atomic(new_capacity.to_u64)
    else
      @buffer = @buffer.realloc(new_capacity.to_u64)
    end
    recalculate_capacity
  end

  def initialize(initial_capacity : Int = 0)
    if initial_capacity > 0
      @buffer = Pointer(T).malloc_atomic(initial_capacity.to_u64)
      recalculate_capacity
    end
  end

  def self.build(capacity : Int) : self
    ary = Array(T).new(capacity)
    ary.write_barrier do
      ary.size = (yield ary.to_unsafe).to_i
    end
    ary
  end

  def self.new(size : Int, &block : Int32 -> T)
    Array(T).build(size) do |buffer|
      size.to_i.times do |i|
        buffer[i] = yield i
      end
      size
    end
  end

  def shift
    return nil if size == 0
    write_barrier do
      retval = to_unsafe[0]
      LibC.memmove(to_unsafe,
        to_unsafe + 1,
        sizeof(T) * (self.size - 1))
      @size -= 1
      retval
    end
  end

  def each(&block)
    @size.times do |i|
      yield @buffer[i]
    end
  end

  def reverse_each
    i = size - 1
    while i >= 0
      yield @buffer[i]
      i -= 1
    end
  end

  def clone
    Array(T).build(size) do |buffer|
      size.times do |i|
        buffer[i] = to_unsafe[i]
      end
      size
    end
  end

  def [](idx : Int)
    abort "accessing out of bounds!" unless 0 <= idx < @size
    @buffer[idx]
  end

  def []?(idx : Int) : T?
    return nil unless 0 <= idx < @size
    @buffer[idx]
  end

  def []=(idx : Int, value : T)
    abort "accessing out of bounds!" unless 0 <= idx < @size
    @buffer[idx] = value
  end

  def push(value : T)
    write_barrier do
      if @size < @capacity
        @buffer[@size] = value
      else
        expand(@size + 1)
        @buffer[@size] = value
      end
      @size += 1
    end
  end

  def pop
    return nil if @size == 0
    write_barrier do
      retval = @buffer[@size]
      @size -= 1
      retval
    end
  end

  def delete(obj)
    select! do |other|
      other != obj
    end
  end

  def delete_at(idx : Int)
    return false unless 0 <= idx < size
    write_barrier do
      if idx == size - 1
        @size -= 1
      else
        LibC.memmove(to_unsafe + idx, to_unsafe + idx + 1,
          sizeof(T) * (size - idx - 1))
      end
    end
    true
  end

  def clear
    @size = 0
  end

  def to_slice
    Slice(T).new(@buffer, @size)
  end

  def sort!
    to_slice.sort!
  end

  def select!(&block)
    write_barrier do
      i = 0
      while i < @size
        unless yield to_unsafe[i]
          LibC.memmove(to_unsafe + i, to_unsafe + i + 1,
            sizeof(T) * (@size - i - 1))
          @size -= 1
        else
          i += 1
        end
      end
    end
  end

  def mark(&block)
    return if @buffer.null?
    yield @buffer.as(Void*)
    {% unless T < Int || T < Struct %}
      each do |obj|
        yield obj.as(Void*)
      end
    {% end %}
  end
end

require "./pipe/circular_buffer.cr"

module PipeFS
  extend self

  class Node < VFS::Node
    include VFS::Child(Node)

    getter! name : String
    getter fs : VFS::FS

    def initialize(@name : String,
                   @m_pid,
                   @parent : PipeFS::Root,
                   @fs : PipeFS::FS,
                   anonymous = false)
      if anonymous
        @open_count = 1
        @attributes |= VFS::Node::Attributes::Anonymous
      end
      @pipe = CircularBuffer.new
    end

    def close
      if anonymous?
        @open_count -= 1
        if @open_count == 1 && (queue = @queue)
          queue.keep_if do |msg|
            msg.unawait (-1).to_u64
            false
          end
        elsif @open_count == 0
          remove
        end
      end
    end

    def clone
      @open_count += 1
    end

    @[Flags]
    enum Flags : UInt32
      WaitRead = 1 << 0
      M_Read   = 1 << 1
      S_Read   = 1 << 2
      M_Write  = 1 << 3
      S_Write  = 1 << 4
      G_Read   = 1 << 5
      G_Write  = 1 << 6
    end

    @flags = Flags::None
    @m_pid = 0
    @s_pid = 0
    @open_count = 0

    def size : Int
      @pipe.size
    end

    def remove : Int32
      return VFS_ERR if removed?
      @parent.as!(Root).remove_child self unless anonymous?
      @pipe.deinit_buffer
      @attributes |= VFS::Node::Attributes::Removed
      VFS_OK
    end

    @queue : VFS::Queue? = nil
    getter! queue

    def read(slice : Slice, offset : UInt32,
             process : Multiprocessing::Process? = nil) : Int32
      return VFS_EOF if removed?

      process = process.not_nil!
      unless @flags.includes?(Flags::G_Read)
        if process.pid == @m_pid
          return 0 unless @flags.includes?(Flags::M_Read)
        elsif process.pid == @s_pid
          return 0 unless @flags.includes?(Flags::S_Read)
        else
          return 0
        end
      end

      if anonymous? && @open_count == 1 && size == 0
        return VFS_EOF
      end

      if @flags.includes?(Flags::WaitRead) && size == 0
        if @queue.nil?
          @queue = VFS::Queue.new
        end
        return VFS_WAIT_QUEUE
      end

      @pipe.read slice
    end

    def write(slice : Slice, offset : UInt32,
              process : Multiprocessing::Process? = nil) : Int32
      return VFS_EOF if removed?

      process = process.not_nil!
      unless @flags.includes?(Flags::G_Write)
        if process.pid == @m_pid
          return 0 unless @flags.includes?(Flags::M_Write)
        elsif process.pid == @s_pid
          return 0 unless @flags.includes?(Flags::S_Write)
        else
          return 0
        end
      end

      if @flags.includes?(Flags::WaitRead)
        if (queue = @queue) && (msg = queue.dequeue)
          retval = msg.respond(slice)
          msg.unawait retval
          return retval
        end
      end

      @pipe.write slice
    end

    def available?(process : Multiprocessing::Process) : Bool
      return true if removed?
      size > 0
    end

    def ioctl(request : Int32, data : UInt64,
              process : Multiprocessing::Process? = nil) : Int32
      return -1 unless process.not_nil!.pid == @m_pid
      return -1 if removed?
      case request
      when SC_IOCTL_PIPE_CONF_FLAGS
        @flags = Flags.new(data.to_u32)
        0
      when SC_IOCTL_PIPE_CONF_PID
        @s_pid = data.to_i32
      else
        -1
      end
    end
  end

  class Root < VFS::Node
    include VFS::Enumerable(Node)

    getter fs : VFS::FS
    getter first_child

    def initialize(@fs : PipeFS::FS)
      @attributes |= VFS::Node::Attributes::Directory
    end

    def create(name : Slice,
               process : Multiprocessing::Process? = nil,
               options : Int32 = 0) : VFS::Node?
      if (options & VFS_CREATE_ANON) != 0
        return PipeFS::Node.new(String.new(name),
          process.not_nil!.pid,
          self, fs,
          anonymous: true)
      end
      node = PipeFS::Node.new(String.new(name),
        process.not_nil!.pid,
        self, fs)
      add_child node
      node
    end
  end

  class FS < VFS::FS
    getter! root : VFS::Node

    def name : String
      "pipes"
    end

    def initialize
      @root = PipeFS::Root.new self
    end
  end

end

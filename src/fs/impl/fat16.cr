require "./fat/cache.cr"

module Fat16FS
  extend self

  MBR_TYPE = 0x06

  private lib Data
    @[Packed]
    struct BootSector
      jmp : UInt8[3]
      oem : UInt8[8]
      sector_size : UInt16
      sectors_per_cluster : UInt8
      reserved_sectors : UInt16
      number_of_fats : UInt8
      root_dir_entries : UInt16
      total_sectors_short : UInt16
      media_descriptor : UInt8
      fat_size_sectors : UInt16
      sectors_per_track : UInt16
      number_of_heads : UInt16
      hidden_sectors : UInt32
      total_sectors_long : UInt32

      drive_number : UInt8
      current_head : UInt8
      boot_signature : UInt8
      volume_id : UInt32
      volume_label : UInt8[11]
      fs_type : UInt8[8]
      boot_code : UInt8[448]
      boot_sector_signature : UInt16
    end

    @[Packed]
    struct Entry
      name : UInt8[8]
      ext : UInt8[3]
      attributes : UInt8
      reserved : UInt8[10]
      modify_time : UInt16
      modify_date : UInt16
      starting_cluster : UInt16
      file_size : UInt32
    end

    @[Packed]
    struct LFNEntry
      seq_number : UInt8
      name_1 : UInt16[5]
      attributes : UInt8
      type : UInt8
      checksum : UInt8
      name_2 : UInt16[6]
      starting_cluster : UInt16
      name_3 : UInt16[2]
    end
  end

  # entry attributes
  protected def entry_exists?(entry : Data::Entry)
    # 0x0 : null entry, 0xE5 : deleted
    entry.name[0] != 0x0 && entry.name[0] != 0xE5
  end

  protected def entry_volume_label?(entry : Data::Entry)
    (entry.attributes & 0x08) == 0x08
  end

  protected def entry_file?(entry : Data::Entry)
    (entry.attributes & 0x18) == 0
  end

  protected def entry_dir?(entry : Data::Entry)
    (entry.attributes & 0x18) == 0x10
  end

  # entry naming
  protected def name_from_entry(entry)
    # name
    name_len = 7
    while name_len >= 0
      break if entry.name[name_len] != ' '.ord.to_u8
      name_len -= 1
    end

    # extension
    ext_len = 2
    while ext_len >= 0
      break if entry.ext[ext_len] != ' '.ord.to_u8
      ext_len -= 1
    end

    # filename
    if ext_len > 0
      builder = String::Builder.new(name_len + 2 + ext_len + 1)
    else
      builder = String::Builder.new(name_len + 1)
    end
    (name_len + 1).times do |i|
      if 'A'.ord <= entry.name[i] <= 'Z'.ord
        # to lower case
        builder.write_byte(entry.name[i] - 'A'.ord + 'a'.ord)
      else
        builder.write_byte(entry.name[i])
      end
    end
    if ext_len > 0
      builder << "."
      (ext_len + 1).times do |i|
        if 'A'.ord <= entry.ext[i] <= 'Z'.ord
          # to lower case
          builder.write_byte(entry.ext[i] - 'A'.ord + 'a'.ord)
        else
          builder.write_byte(entry.ext[i])
        end
      end
    end

    builder.to_s
  end

  class Node < VFS::Node
    include FatCache
    include VFS::Child(Node)
    include VFS::Enumerable(Node)

    @name : String? = nil
    property name

    def first_child
      if directory? && !@dir_populated
        @dir_populated = true
        populate_directory
      end
      @first_child
    end

    @size = 0u32
    getter size

    # file system specific
    @starting_cluster = 0u32
    getter starting_cluster

    @dir_populated = false
    getter dir_populated

    getter fs : VFS::FS

    def initialize(@fs : FS, @name = nil, directory = false,
                   @next_node = nil, @first_child = nil,
                   @size = 0u32, @starting_cluster = 0u32)
      if directory
        @attributes |= VFS::Node::Attributes::Directory
      end
    end

    # read
    private def sector_for(cluster)
      fs.fat_sector + cluster // fs.fat_sector_size
    end

    private def ent_for(cluster)
      cluster % fs.fat_sector_size
    end

    private def read_fat_table(fat_table, cluster, last_sector? = -1)
      fat_sector = sector_for cluster
      if last_sector? == fat_sector
        return fat_sector
      end

      fs.device.read_sector(fat_table.to_unsafe.as(UInt8*), fat_sector.to_u64)
      fat_sector
    end

    def read_buffer(read_size = 0, offset : UInt32 = 0, allocator : StackAllocator? = nil, &block)
      return if directory?

      # check arguments
      if read_size == 0
        read_size = size
      elsif read_size < 0
        return
      end
      if offset + read_size > size
        read_size = size - offset
      end

      # setup
      fat_table = if allocator
                    sz = fs.fat_sector_size
                    Slice(UInt16).new(allocator.not_nil!.malloc(sz * sizeof(UInt16)).as(UInt16*), sz)
                  else
                    Slice(UInt16).malloc(fs.fat_sector_size)
                  end
      fat_sector = read_fat_table fat_table, starting_cluster

      cluster = starting_cluster
      remaining_bytes = read_size

      # skip clusters
      offset_factor = fs.sectors_per_cluster * 512
      if cached_cluster = get_cache(offset.to_i32)
        cluster = cached_cluster
        fat_sector = read_fat_table fat_table, cluster
      else
        offset_clusters = offset // offset_factor
        while offset_clusters > 0 && cluster < 0xFFF8
          fat_sector = read_fat_table fat_table, cluster, fat_sector
          cluster = fat_table[ent_for cluster]
          offset_clusters -= 1
        end
      end
      offset_bytes = offset % offset_factor

      # read file
      cluster_bufsz = 512 * fs.sectors_per_cluster
      cluster_buffer = if allocator.nil?
                         Slice(UInt8).malloc(cluster_bufsz)
                       else
                         Slice(UInt8).new(allocator.not_nil!.malloc(cluster_bufsz).as(UInt8*), cluster_bufsz)
                       end
      last_cluster = 0
      begin
        while remaining_bytes > 0 && cluster < 0xFFF8
          if offset_bytes <= cluster_buffer.size
            # read the sector
            sector = ((cluster.to_u64 - 2) * fs.sectors_per_cluster) + fs.data_sector
            retval = fs.device.read_sector(cluster_buffer.to_unsafe, sector, fs.sectors_per_cluster)
            unless retval
              Serial.print "unable to read from device, returning garbage!"
              remaining_bytes = 0
              break
            end

            # yield the read buffer
            cur_buffer = Slice(UInt8).new(cluster_buffer.to_unsafe + offset_bytes,
              Math.min(cluster_buffer.size - offset_bytes, remaining_bytes.to_i32))
            yield cur_buffer
            offset += cur_buffer.size
            remaining_bytes -= cur_buffer.size
            offset_bytes = 0
          else
            offset_bytes -= cluster_buffer.size
          end
          fat_sector = read_fat_table fat_table, cluster, fat_sector
          last_cluster = cluster
          cluster = fat_table[ent_for cluster]
        end
      ensure
        # set cache and clear allocation
        insert_cache offset, last_cluster.to_u32
        if allocator
          allocator.not_nil!.clear
        end
      end
    end

    def read(read_size = 0, offset : UInt32 = 0, allocator : StackAllocator? = nil, &block)
      read_buffer(read_size, offset, allocator) do |buffer|
        buffer.each do |byte|
          yield byte
        end
      end
    end

    def fat_populate_directory(allocator : StackAllocator? = nil)
      return if @dir_populated
      @dir_populated = true
      @lookup_cache = LookupCache.new

      fat_table = if allocator
                    Slice(UInt16).mmalloc_a fs.fat_sector_size, allocator.not_nil!
                  else
                    Slice(UInt16).malloc fs.fat_sector_size
                  end
      fat_sector = read_fat_table fat_table, starting_cluster

      cluster = starting_cluster
      end_directory = false

      entries = Slice(Data::Entry).malloc 16

      while cluster < 0xFFF8
        sector = ((cluster.to_u64 - 2) * fs.sectors_per_cluster) + fs.data_sector
        read_sector = 0
        while read_sector < fs.sectors_per_cluster
          fs.device.read_sector(entries.to_unsafe.as(UInt8*), sector + read_sector)
          entries.each do |entry|
            load_entry(entry)
          end
          read_sector += 1
        end

        break if end_directory
        fat_sector = read_fat_table fat_table, cluster, fat_sector
        cluster = fat_table[ent_for cluster]
      end

      each_child do |node|
        lookup_cache[node.name.not_nil!] = node.as(VFS::Node)
      end

      # clean up within function call
      if allocator
        allocator.not_nil!.clear
      end
    end

    def populate_directory : Int32
      if Ide.locked?
        VFS_WAIT
      else
        fat_populate_directory
        VFS_OK
      end
    end

    def read(slice : Slice, offset : UInt32,
             process : Multiprocessing::Process? = nil) : Int32
      unless directory?
        init_cache
      end
      if offset >= @size
        return VFS_EOF
      end
      VFS_WAIT
    end

    def spawn(udata : Multiprocessing::Process::UserData) : Int32
      return VFS_ERR if directory?
      init_cache
      VFS_WAIT
    end

    def write(slice : Slice, offset : UInt32,
              process : Multiprocessing::Process? = nil) : Int32
      return VFS_ERR if directory?
      VFS_ERR
    end

    @lfn_segments : Array(String)? = nil
    private getter! lfn_segments
    @lfn_length = 0

    private def lfn_finish
      builder = String::Builder.new @lfn_length
      lfn_segments.reverse_each do |segment|
        builder << segment
      end
      @lfn_segments = nil
      @lfn_length = 0
      builder.to_s
    end

    # entry loading
    def load_entry(entry)
      if entry.attributes == 0xF
        if @lfn_segments.nil?
          @lfn_segments = Array(String).new
          @lfn_length = 0
        end
        lfn_entry = entry.unsafe_as(Data::LFNEntry)
        return if lfn_entry.seq_number == 0xE5
        builder = String::Builder.new 13
        ended = false
        lfn_entry.name_1.each do |word|
          if word == 0xFFFF
            ended = true
            break
          end
          builder << word.unsafe_chr
        end
        lfn_entry.name_2.each do |word|
          if word == 0xFFFF || ended
            ended = true
            break
          end
          builder << word.unsafe_chr
        end
        lfn_entry.name_3.each do |word|
          if word == 0xFFFF || ended
            ended = true
            break
          end
          builder << word.unsafe_chr
        end
        str = builder.to_s
        @lfn_length += str.size
        lfn_segments.push str
        return
      elsif @lfn_length > 0
        lfn_name = lfn_finish
      end
      return if !Fat16FS.entry_exists? entry
      return if Fat16FS.entry_volume_label? entry
      unless 0x20 <= entry.name[0] && entry.name[0] <= 0x7e
        return
      end
      if Fat16FS.entry_file? entry
        load_file_entry entry, lfn_name
      elsif Fat16FS.entry_dir? entry
        load_dir_entry entry, lfn_name
      end
    end

    private def load_file_entry(entry, lfn_name = nil)
      node = Node.new(fs, lfn_name || Fat16FS.name_from_entry(entry),
        starting_cluster: entry.starting_cluster.to_u32,
        size: entry.file_size)
      add_child node
    end

    private def load_dir_entry(entry, lfn_name = nil)
      name = Fat16FS.name_from_entry(entry)
      return if name == "." || name == ".."
      node = Node.new(fs, lfn_name || name, true,
        starting_cluster: entry.starting_cluster.to_u32,
        size: entry.file_size)
      add_child node
    end
  end

  class FS < VFS::FS
    @fat_sector = 0u32
    getter fat_sector
    @fat_sector_size = 0
    getter fat_sector_size

    @data_sector = 0u64
    getter data_sector

    @sectors_per_cluster = 0u64
    getter sectors_per_cluster

    getter! root : VFS::Node
    getter device

    @name = ""
    getter name : String

    def initialize(@device : Ata::Device,
                   partition : MBR::Data::PartitionTable, idx : Int)
      abort "device must be ATA" if @device.type != Ata::Device::Type::Ata

      builder = String::Builder.new
      builder << @device.not_nil!.name
      builder << 'p'
      builder << idx
      @name = builder.to_s

      bs = Pointer(Data::BootSector).malloc_atomic

      device.read_sector(bs.as(UInt8*), partition.first_sector.to_u64)

      @fat_sector = partition.first_sector + bs.value.reserved_sectors
      @fat_sector_size = bs.value.sector_size.to_i32 // sizeof(UInt16)

      root_dir_sectors = ((bs.value.root_dir_entries * 32) + (bs.value.sector_size - 1)) // bs.value.sector_size

      sector = (fat_sector + bs.value.fat_size_sectors * bs.value.number_of_fats).to_u64
      @data_sector = sector + root_dir_sectors
      @sectors_per_cluster = bs.value.sectors_per_cluster.to_u64

      # load root directory
      @root = Node.new self, nil, true
      entries = Slice(Data::Entry).malloc 16

      bs.value.root_dir_entries.times do |i|
        break if sector + i > @data_sector
        device.read_sector(entries.to_unsafe.as(UInt8*), sector + i)
        entries.each do |entry|
          if pointerof(entry).as(UInt8*)[0] == 0
            break
          end
          root.load_entry entry
        end
      end

      # setup process-local variables
      @process_allocator =
        StackAllocator.new(Pointer(Void).new(Multiprocessing::KERNEL_HEAP_INITIAL))
      @process = Multiprocessing::Process
        .spawn_kernel("[fat16fs]",
          ->(ptr : Void*) { ptr.as(FS).process },
          self.as(Void*),
          stack_pages: 4) do |process|
        Paging.alloc_page(Multiprocessing::KERNEL_HEAP_INITIAL, true, false, 2)
      end

      @queue = VFS::Queue.new(@process)
    end

    # queue
    getter queue

    protected def process
      while true
        if (msg = @queue.not_nil!.dequeue)
          node = msg.vfs_node.as!(Node)
          case msg.type
          when VFS::Message::Type::Read
            node.read_buffer(msg.slice_size,
              msg.file_offset.to_u32,
              allocator: @process_allocator) do |buffer|
              msg.respond(buffer)
            end
            msg.unawait
          when VFS::Message::Type::Spawn
            udata = msg.udata.not_nil!
            case (retval = ElfReader.load_from_kernel_thread(node, @process_allocator.not_nil!))
            when ElfReader::Result
              retval = retval.as(ElfReader::Result)
              pid = Multiprocessing::Process.spawn_user_drv(udata, retval)
              if msg.process
                msg.unawait(pid)
              end
            else
              Serial.print "unable to execute: ", retval, "\n"
              if msg.process
                msg.unawait(ENOEXEC)
              end
            end
            @process_allocator.not_nil!.clear
          when VFS::Message::Type::PopulateDirectory
            node.fat_populate_directory(allocator: @process_allocator)
            msg.unawait_rewind
          end
        else
          Multiprocessing.sleep_disable_gc
        end
      end
    end
  end
end

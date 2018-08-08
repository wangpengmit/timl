#!/usr/bin/env ruby

def breakup(n, s)
  if n <= 0 then
    return [s]
  end
  len = s.size
  i = 0
  acc = []
  while i < len
    acc << s[i...i+n]
    i = i + n
  end
  acc
end
    
def filter(s)
  s.gsub(/(0x|--input[ ]+[0-9a-fA-F]{8})([0-9a-fA-F]+)/){
    $1 + "\n" + breakup(64, $2).join("\n")
  }
end

# while gets
#   puts (filter $_)
# end

require 'open3'

if ARGV.length == 0 then
  puts "Usage: THIS command arguments"
  exit
end

cmd = ARGV.join " "

puts ("Running cmd: " + filter(cmd))

Open3.popen2e(cmd) do |stdin, stdout_err, wait_thr|
  while line = stdout_err.gets
    puts (filter line)
  end

  exit_status = wait_thr.value
  unless exit_status.success?
    abort
  end
end

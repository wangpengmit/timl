#!/usr/bin/env ruby

def filter(s)
  s.gsub(/\.t\.sml/, ".sml")
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

Open3.popen2e(cmd) do |stdin, stdout_err, wait_thr|
  while line = stdout_err.gets
    puts (filter line)
  end

  exit_status = wait_thr.value
  unless exit_status.success?
    abort
  end
end

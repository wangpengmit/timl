#!/usr/bin/env ruby

template = 
%q{
Token      & 0.005 & 1.755& 0.004      & 0.184     \\
Crowdsale  & 0.004 & 0.485& 0.003      & 0.057     \\
EtherDelta & 0.102 & 4.903& 0.022      & 0.367     \\
Congress   & 0.064 & 11.381       & 0.025      & 2.033     \\
MultiSig   & 0.208 & 20.802       & 0.212      & 8.818     \\
CryptoKitties      & 0.555 & 65.766       & 0.303      & 31.837    \\
BlindAuction       & 0.312 & 8.253& 0.007      & 1.009     \\
SafeRemotePurchase & 0.039 & 7.759& 0.006      & 0.878 
}

template = template.split("\n").join("")

lines = template.split(%q{\\})

lines = lines.map do |line|
  line.split('&').map do |x| x.strip end
end

subjects = lines.map do |x| x[0] end
descriptions = lines.map do |x| x[1] end

# The 'list' case will generate an error because module "List" exists in stdlib. The time reported will be the time for typechecking stdlib, which can represent (overestimate) the time for typechecking list.timl

results = subjects.zip(descriptions).map do |(sub, desc)|
  fn = "#{sub}.etiml"
  contents = File.open(fn).readlines
  contents.select! {|ln| not (ln =~ /^\s*$|^\s*\(\*.*\*\)\s*$/) }
  [sub, contents.length.to_s, contents.count { |ln| (ln =~ /absidx|idx|using/) != nil }.to_s]
end

File.open("loc.csv", "w") do |f|
  f.puts "Example,LOC,LOC containing time annotations"
  results.each do |result|
    f.puts result.join(",")
  end
end

puts
results.each do |line|
  line = line.join(" & ")
  line = line + " \\\\"
  puts line
end
puts

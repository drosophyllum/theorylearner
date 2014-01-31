#! /usr/bin/perl

use threads; 

for $buffersize (1..5){
	for $erd (0,0.2,0.4,0.6,0.8,1){
		threads->create(\&body,$buffersize,$erd);
	}
}

sub body {
		$buffersize = shift @_; 
		$erd = shift @_;
		$_ = `./thera $buffersize $erd`;
		print;
}

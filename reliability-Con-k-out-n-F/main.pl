#!/usr/bin/perl
#
# Computing the Reliability of Consecutive-k-out-of-n: F Systems
#
# by Min-Sheng Lin
#
$|=1;

#globals
$n=10000;
$k=500;
$p=0.01;
$q=1-$p;
%M=();
%I=();

print "\n== Comupte the reliability of Con/$k/$n:F system (p=$p) ==\n";
print "our proposed algorithm   :";
($linear1, $circular1)=&compute_rel_con_k_out_n_F();
print "RL=$linear1  RC=$circular1\n";

print "the brute-force algorithm:";
($linear2, $circular2)=&brute_force();
print "RL=$linear2  RC=$circular2\n";
 
# apply our proposed algorithm in O(k^2*log(n)) time
sub compute_rel_con_k_out_n_F {  
  %M=();
  %I=();  
  # set the first row of matrix M
  for ($j=1,$tmp=$p; $j <= $k ; $j++, $tmp *= $q){
     $M{1,$j}=$tmp;     
     if ( $j==1 ){
        $I{1,$j}=1;
     }else{
        $I{1,$j}=0;
     }
  }
  # set the other entries of matrix M
  for ($i=2 ; $i <= $k ; $i++){
    for ($j=1 ; $j <= $k ; $j++ ){
        if ( $i == $j+1 ){
           $M{$i, $j}=1;
        }else{
           $M{$i, $j}=0;
        }
        if ($i == $j){
           $I{$i,$j}=1;
        }else{
           $I{$i,$j}=0;
        } 
    }
  }

  *m=&fast_matrix_power();
  
  for ($i=1, $tmp=$q ; $i <= $k ; $i++, $tmp*=$q){    
	if ($i== $k){
      $linear[$k-$i+1]=1-$tmp;
    }else{
      $linear[$k-$i+1]=1;
    }
	$circular[$k-$i+1]=1-$tmp;    
  }

  $rel_L=0;
  $rel_C=0;
  for ($i=1 ; $i <= $k ; $i++){    
    $rel_L += $m{1,$i}*$linear[$i];
    $rel_C += $m{1,$i}*$circular[$i];
  }
  return($rel_L, $rel_C);
}

sub fast_matrix_power {  
  %mx=%M;
  %m2=%I;  
  #convert the value of (n-k) to binary 
  $bits=unpack("B*",pack("N",$n-$k));
  $bits=~s|^0+||;
  @bit=split("",$bits);
  @bit=reverse(@bit);
  
  foreach $bit (@bit){
    if ($bit eq '1'){
       *m2=&maxtrix_multiple(*m2,*mx);
    }
    *mx=&maxtrix_multiple(*mx,*mx);
  }
  return(*m2);
}

sub maxtrix_multiple {
  local(*ma, *mb)=@_;
  local(*mc);
 # set last row
  for ($j=1 ; $j <= $k ; $j++ ) {
    $tmp=0;
    for ($x=1 ; $x <= $k ; $x++){
      $tmp += $ma{$k,$x}*$mb{$x, $j};
    }    
    $mc{$k, $j}=$tmp;
  }

  for ($i=$k-1 ; $i >= 1; $i--){
    for ( $j=$k ; $j >= 1 ; $j--){
      if ( $j == $k ){
        $mc{$i, $j}=$M{1,$j}*$mc{$i+1,1};
      }else{
        $mc{$i,$j}=$M{1,$j}*$mc{$i+1,1}+$mc{$i+1,$j+1};  
      }
    }
  }         
  return(*mc);
}

# apply the brute-force algorithm in O(2^n) time
sub brute_force {
  return("--","--") if ($n > 20);
  $max=(1 << $n);
  $rel_L=0;
  $rel_C=0;
  for ($i=0 ; $i < $max ; $i++){
      $bits=unpack("B*",pack("N",$i));
      $bits=substr($bits,-1*$n,$n);
      @bit=split("",$bits);
      $flag2='success';
      $xflag2='success'; 
      for ($j=0 ; $j < $n ; $j++){          
          $flag='fail';
          $xflag='fail';          
          for ($h=0; $h < $k ; $h++){
             $h1=($j+$h) % $n;
             if ( $bit[$h1] eq '1' ){
                $flag='success';
                $xflag='success';
                break;          
             }
          } # for $h
          if ($flag eq 'fail'){
             $flag2='fail';          
          }
          if ($xflag eq 'fail' && $j <= ($n-$k) ){
             $xflag2='fail';
          }
      } # for j
	  
      $tmp=0;
      if ($flag2 eq 'success'){
         $tmp=1;
         for ($j=0 ; $j < $n ; $j++){
             if ($bit[$j] eq '1'){
                $tmp *= $p;
             }else{
                $tmp *= $q;
             }  
         } # for j
         $rel_C += $tmp;
      }

      $xtmp=0.0;

      if ($xflag2 eq 'success'){
         $xcount++;
         $xtmp=1;
         for ($j=0 ; $j < $n ; $j++){
             if ($bit[$j] eq '1'){
                $xtmp *= $p;
             }else{
                $xtmp *= $q;
             }  
         } # for j
         $rel_L += $xtmp;
      } 
  }  # for i  
  return($rel_L, $rel_C);
} 
